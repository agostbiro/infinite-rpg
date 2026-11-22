"""Exact, finite-state graph generation. No simulation is used for validation."""
from collections import defaultdict, deque
from fractions import Fraction as Q
from functools import lru_cache
import hashlib
import json
import time
import scenes

COUNTS = [1, 3, 6, 10, 15, 21, 25, 27, 27, 25, 21, 15, 10, 6, 3, 1]
HP_LIMIT = 6
GRID = 3
HERO_LEVEL = 12
MAX_NODES = 60
MAX_CHARACTERS = 12


def fraction(q):
    q = Q(q)
    return str(q.numerator) if q.denominator == 1 else f"{q.numerator}/{q.denominator}"


def success(level, roll):
    if roll <= 4:
        return "critical"
    if roll == 18 or roll == 17 or roll >= level + 10:
        return "failure"
    if (roll == 5 and level >= 15) or (roll == 6 and level >= 16):
        return "critical"
    return "success" if roll <= level else "failure"


def encode(s):
    a, b, turn, guard = s
    return (((a * (GRID + 1) + b) * 2 + turn) * 2 + int(guard))


def decode(i):
    guard, i = i % 2, i // 2
    turn, i = i % 2, i // 2
    return (i // (GRID + 1), i % (GRID + 1), turn, guard)


def combine(entries):
    out = defaultdict(Q)
    for state, p in entries:
        out[state] += p
    return dict(sorted((s, p) for s, p in out.items() if p))


WEAPONS = ("punch", "largeKnife", "broadsword")


def attack_level(dx, weapon):
    return dx - {"punch": 0, "largeKnife": 4, "broadsword": 5}[weapon]


def injury(weapon, face):
    if weapon == "punch":
        return max(0, face - 3)
    if weapon == "largeKnife":
        return 2 * max(1, face - 2)
    if weapon == "broadsword":
        return max(1, face + 1) * 3 // 2
    raise ValueError("Unsupported weapon.")


def recovery_actions(heal, direct, iq):
    # Two distinct actions: IQ improves the first; the GM counterbalances the
    # second. Their uniform average is unchanged. Both supports stay positive.
    p = Q(iq, 20)
    return {"Careful recovery": combine(((heal,p),(direct,1-p))),
            "Bold recovery": combine(((heal,1-p),(direct,p)))}


def additional_checks(world, maximum):
    neighbors = [set() for _ in world["rows"]]
    deterministic = total = 0
    for s, row in enumerate(world["rows"]):
        for v, p in row.items():
            if not p or (v == s and world["terminal"][s]):
                continue
            if v == s:
                raise ValueError("A live self-loop violates noSmallCycles.")
            neighbors[s].add(v); neighbors[v].add(s)
        if not world["terminal"][s]:
            for action in world["choices"][s].values():
                total += 1
                deterministic += sum(p > 0 for p in action.values()) == 1
    for a, ns in enumerate(neighbors):
        for b in ns:
            if ns & neighbors[b]:
                raise ValueError("An undirected triangle violates noSmallCycles.")
    if not 0 <= maximum <= 1 or deterministic > maximum * total:
        raise ValueError("Too many deterministic actions for the fixed graph contract.")
    return dict(no_small_cycles=True, deterministic=deterministic, decisions=total,
                fraction=fraction(Q(deterministic, total)) if total else "0",
                maximum=fraction(maximum))


def combat_actions(s, enemy_level, hero_level=HERO_LEVEL, hero_weapon="punch", enemy_weapon="punch"):
    """Unarmed ST10, HT10. Main's 3d6 attack/dodge and thr-1 crushing damage.

    Both fighters choose uniformly among Attack and Defend. The prototype has
    no carried items, so no bonus action is enabled. Defend protects the actor
    while the other fighter still takes their turn.
    """
    a, b, turn, guarded = s
    if not a or not b:
        return {"Terminal": {encode(s): Q(1)}}
    weapon = hero_weapon if turn == 0 else enemy_weapon
    dx = hero_level if turn == 0 else enemy_level
    level = attack_level(dx, weapon)
    defender_level = enemy_level if turn == 0 else hero_level
    defender_hp = b if turn == 0 else a
    dodge = (defender_level + 10) // 4 + 3
    if 3 * defender_hp < HP_LIMIT:
        dodge = (dodge + 1) // 2
    dodge += 2 if guarded else 0
    dodge_prob = sum((Q(c, 216) for r, c in zip(range(3, 19), COUNTS)
                      if success(dodge, r) != "failure"), Q(0))
    damage = defaultdict(Q)
    for roll, count in zip(range(3, 19), COUNTS):
        p = Q(count, 216)
        result = success(level, roll)
        if result == "failure":
            damage[0] += p
        elif roll == 3:
            damage[injury(weapon, 6)] += p
        else:
            hit = Q(1) if result == "critical" else 1 - dodge_prob
            damage[0] += p * (1 - hit)
            for face in range(1, 7):
                damage[injury(weapon, face)] += p * hit / 6
    attacks = []
    for hit, p in damage.items():
        next_s = (a, max(0, b - hit), 1, 0) if turn == 0 else (max(0, a - hit), b, 0, 0)
        attacks.append((encode(next_s), p))
    defend = encode((a, b, 1 - turn, 1))
    return {"Attack": combine(attacks), "Defend": {defend: Q(1)}}


def uniform_row(actions):
    return combine((v, p / len(actions)) for row in actions.values() for v, p in row.items())


def combat_raw_row(s, enemy_level, hero_level=HERO_LEVEL, hero_weapon="punch", enemy_weapon="punch"):
    """Sparse row in the exact order used by Lean's executable duelRows."""
    a, b, turn, guard = s
    if not a or not b:
        return [(encode(s), Q(1))]
    weapon = hero_weapon if turn == 0 else enemy_weapon
    dx = hero_level if turn == 0 else enemy_level
    level = attack_level(dx, weapon)
    defender = enemy_level if turn == 0 else hero_level
    hp = b if turn == 0 else a
    dodge = (defender + 10) // 4 + 3
    if 3 * hp < HP_LIMIT:
        dodge = (dodge + 1) // 2
    dodge += 2 if guard else 0
    dp = sum((Q(c,216) for r,c in zip(range(3,19),COUNTS) if success(dodge,r) != "failure"), Q(0))
    ordinary = sum((Q(c,216) for r,c in zip(range(3,19),COUNTS) if success(level,r) == "success"), Q(0))
    critical = sum((Q(c,216) for r,c in zip(range(3,19),COUNTS) if r != 3 and success(level,r) == "critical"), Q(0))
    hit, maximized = critical + ordinary * (1-dp), Q(1,216)
    def next_hit(d):
        return encode((a,max(0,b-d),1,0) if turn == 0 else (max(0,a-d),b,0,0))
    return [(next_hit(0),(1-maximized-hit)/2)] + [
        (next_hit(injury(weapon,face)),hit/12) for face in range(1,7)] + [
        (next_hit(injury(weapon,6)),maximized/2), (encode((a,b,1-turn,1)),Q(1,2))]


def solve_linear(a, b):
    """Gauss-Jordan over Fraction, with all right-hand sides in one solve."""
    n = len(a)
    m = len(b[0]) if b else 0
    x = [list(a[i]) + list(b[i]) for i in range(n)]
    for k in range(n):
        pivot = next((i for i in range(k, n) if x[i][k]), None)
        if pivot is None:
            raise ValueError("A nonterminating closed class was found in the combat.")
        x[k], x[pivot] = x[pivot], x[k]
        d = x[k][k]
        x[k][k:] = [v / d for v in x[k][k:]]
        for i in range(n):
            if i != k and x[i][k]:
                c = x[i][k]
                x[i][k:] = [x[i][j] - c * x[k][j] for j in range(k, n + m)]
    return [r[n:] for r in x]


def path_certificate(rows, terminal):
    reverse = defaultdict(list)
    for s, row in enumerate(rows):
        for v, p in row.items():
            if p > 0:
                reverse[v].append(s)
    rank = [None] * len(rows)
    nxt = list(range(len(rows)))
    queue = deque()
    for s, term in enumerate(terminal):
        if term:
            rank[s] = 0
            queue.append(s)
    while queue:
        v = queue.popleft()
        for s in reverse[v]:
            if rank[s] is None:
                rank[s] = rank[v] + 1
                nxt[s] = v
                queue.append(s)
    if any(r is None for r in rank):
        raise ValueError("Some states have no positive-probability path to an output.")
    return rank, nxt


@lru_cache(maxsize=128)
def combat(enemy_level, hero_level=HERO_LEVEL, hero_weapon="punch", enemy_weapon="punch"):
    start = time.perf_counter()
    n = 4 * (GRID + 1) ** 2
    states = [decode(i) for i in range(n)]
    actions = [combat_actions(s, enemy_level, hero_level, hero_weapon, enemy_weapon) for s in states]
    rows = [uniform_row(a) for a in actions]
    raw_rows = [combat_raw_row(s, enemy_level, hero_level, hero_weapon, enemy_weapon) for s in states]
    assert all(combine(raw) == row for raw, row in zip(raw_rows, rows))
    terminal = [a == 0 or b == 0 for a, b, _, _ in states]
    # One output per surviving hero HP, plus Lose (output index zero).
    outputs = [a if b == 0 and a else 0 for a, b, _, _ in states]
    live = [i for i in range(n) if not terminal[i]]
    index = {s: i for i, s in enumerate(live)}
    matrix = [[Q(int(i == j)) for j in range(len(live))] for i in range(len(live))]
    rhs = [[Q(0)] * (GRID + 2) for _ in live]
    for s in live:
        i = index[s]
        rhs[i][-1] = 1  # Expected number of internal combat actions.
        for v, p in rows[s].items():
            if terminal[v]:
                rhs[i][outputs[v]] += p
            else:
                matrix[i][index[v]] -= p
    solved = solve_linear(matrix, rhs)
    exit_laws = []
    expectation = []
    for s in range(n):
        if terminal[s]:
            exit_laws.append([Q(int(k == outputs[s])) for k in range(GRID + 1)])
            expectation.append(Q(0))
        else:
            exit_laws.append(solved[index[s]][:-1])
            expectation.append(solved[index[s]][-1])
    rank, nxt = path_certificate(rows, terminal)
    # Independent residual checks before constructing a Lean certificate.
    for s in range(n):
        assert sum(rows[s].values(), Q(0)) == 1 and all(p >= 0 for p in rows[s].values())
        assert sum(exit_laws[s], Q(0)) == 1
        if not terminal[s]:
            for k in range(GRID + 1):
                assert exit_laws[s][k] == sum((p * exit_laws[v][k] for v, p in rows[s].items()), Q(0))
    return dict(level=enemy_level, hero_level=hero_level, hero_weapon=hero_weapon, enemy_weapon=enemy_weapon, states=states, actions=actions, rows=rows, raw_rows=raw_rows,
                terminal=terminal, lose=[a == 0 for a, _, _, _ in states], outputs=outputs,
                exits=exit_laws, expectation=expectation, rank=rank, next=nxt,
                solve_seconds=time.perf_counter() - start)


def build_world(level, enemy_hp, branches=2, event_layers=()):
    """Generate a structural graph. Each layer contains parallel neutral events.

    Neutral events preserve HP. Their number changes the duration law, while
    the calibrated two-combat profile retains the same eventual loss law.
    """
    fight = combat(level)
    depth = len(event_layers)
    nodes, rows, choices, keys, lookup = [], [], [], [], {}

    def add(scene, hp):
        key = (scene, hp)
        if key in lookup:
            return lookup[key]
        idx = len(keys)
        lookup[key] = idx
        keys.append(key)
        rows.append(None)
        choices.append(None)
        if scene == "lose":
            title, kind, column = "Lose", "lose", depth + 6
        elif scene == "win":
            title, kind, column = "Win", "win", depth + 6
        elif scene.startswith("event:"):
            _, layer, branch = scene.split(":")
            title, kind, column = f"Event {int(layer) + 1}.{int(branch) + 1}", "event", int(layer) + 1
        elif scene.startswith("route"):
            num = int(scene[5:])
            title, kind, column = f"Combat 1 · Route {num + 1}", "combat", depth + 1
        else:
            title, kind, column = {
                "camp": ("Start", "scene", 0), "shrine": ("Decision", "scene", depth + 2),
                "rest": ("Recovery", "rest", depth + 3), "boss": ("Combat 2", "combat", depth + 4),
                "treasure": ("Reward", "treasure", depth + 5),
                "detour": ("Challenge", "event", depth + 3),
            }[scene]
        nodes.append(dict(id=idx, scene=scene, hp=hp, title=title, kind=kind, column=column))
        return idx

    add("camp", GRID)
    cursor = 0
    while cursor < len(keys):
        s = cursor
        scene, hp = keys[s]
        opts = {}
        if scene in ("lose", "win"):
            opts = {"End": {s: Q(1)}}
        elif scene == "camp" or scene.startswith("event:"):
            layer = 0 if scene == "camp" else int(scene.split(":")[1]) + 1
            if layer < depth:
                opts = {f"Choose event {layer + 1}.{i + 1}": {add(f"event:{layer}:{i}", hp): Q(1)}
                        for i in range(event_layers[layer])}
            else:
                opts = {f"Take route {i + 1}": {add(f"route{i}", hp): Q(1)} for i in range(branches)}
        elif scene.startswith("route") or scene == "boss":
            ehp = enemy_hp[0 if scene.startswith("route") else 1]
            entry = encode((hp, ehp, 0, 0))
            continuation = "shrine" if scene.startswith("route") else "treasure"
            row = {}
            for after, p in enumerate(fight["exits"][entry]):
                if p:
                    row[add("lose" if after == 0 else continuation, after)] = p
            opts = {"Resolve combat": row}
            nodes[s]["combat"] = dict(level=level, enemy_hp=ehp, entry=entry,
                                       lose=fraction(fight["exits"][entry][0]), reference_lose=fraction(fight["exits"][entry][0]),
                                       expected_actions=float(fight["expectation"][entry]))
        elif scene == "shrine":
            opts = {"Recover 1 HP": {add("rest", min(GRID, hp + 1)): Q(1)},
                    "Continue directly": {add("detour", hp): Q(1)}}
        elif scene in ("rest", "detour"):
            opts = {"Continue to combat": {add("boss", hp): Q(1)}}
        elif scene == "treasure":
            opts = {"Finish": {add("win", hp): Q(1)}}
        if scene == "shrine":
            heal = next(iter(opts["Recover 1 HP"]))
            direct = next(iter(opts["Continue directly"]))
            opts = recovery_actions(heal, direct, 10)
        choices[s] = opts
        rows[s] = uniform_row(opts)
        cursor += 1
    terminal = [n["kind"] in ("win", "lose") for n in nodes]
    lose = [n["kind"] == "lose" for n in nodes]
    rank, nxt = path_certificate(rows, terminal)
    # The event graph is a DAG; only absorbing outputs have self-loops.
    @lru_cache(None)
    def loss(s):
        if terminal[s]:
            return Q(int(lose[s]))
        return sum((p * loss(v) for v, p in rows[s].items()), Q(0))
    losses = [loss(s) for s in range(len(nodes))]
    table = [[Q(int(t)) for t in terminal]]
    loss_table = [[Q(int(t)) for t in lose]]
    for _ in range(8 + depth):
        table.append([Q(1) if terminal[s] else sum((p * table[-1][v] for v, p in row.items()), Q(0))
                      for s, row in enumerate(rows)])
        loss_table.append([Q(1) if lose[s] else sum((p * loss_table[-1][v] for v, p in row.items()), Q(0))
                           for s, row in enumerate(rows)])
    assert all(x == 1 for x in table[-1])
    return dict(nodes=nodes, rows=rows, choices=choices, terminal=terminal, lose=lose,
                losses=losses, table=table, loss_table=loss_table, rank=rank, next=nxt, initial=0,
                level=level, enemy_hp=enemy_hp, event_layers=tuple(event_layers))


@lru_cache(maxsize=3)
def reference(difficulty):
    target = {"easy": Q(1, 2), "medium": Q(7, 10), "hard": Q(9, 10)}[difficulty]
    best = None
    # The target is fixed before generating the narrative and branching layout.
    for level in (10, 12, 14, 16, 8, 18):
        for hp in ((1, 2), (2, 2), (2, 3), (3, 3), (1, 1), (1, 3)):
            world = build_world(level, hp)
            error = abs(world["losses"][0] - target)
            if best is None or error < best[0]:
                best = (error, world)
            if error <= Q(1, 20):
                return target, world
    raise ValueError(f"No admissible calibration found; best error {float(best[0]):.3f}.")


def attach_characters(world, count):
    """Assign distinct identities to graph events; HP variants share identities.

    Extra characters are noncombat participants, not additional simultaneous
    fighters. With only two identities the same opponent occurs in both combats.
    """
    roster = [dict(id=i, name="Player" if i == 0 else f"Character {i + 1}",
                   role="player" if i == 0 else "opponent" if i < 3 else "participant")
              for i in range(count)]
    for node in world["nodes"]:
        node["characters"] = [0]
        if node.get("combat"):
            opponent = 1 if node["scene"].startswith("route") else min(2, count - 1)
            node["characters"].append(opponent)
            node["combat"]["opponent"] = opponent
    scenes = list(dict.fromkeys(n["scene"] for n in world["nodes"]
                               if n["kind"] in ("scene", "event", "rest")))
    for i in range(3, count):
        scene = scenes[(i - 3) % len(scenes)]
        for node in world["nodes"]:
            if node["scene"] == scene:
                node["characters"].append(i)
    return roster


def generate(difficulty="easy", branches=2, max_nodes=24, character_count=4):
    if difficulty not in ("easy", "medium", "hard"):
        raise ValueError("Unknown difficulty.")
    if type(branches) is not int or not 2 <= branches <= 4:
        raise ValueError("Choose between two and four initial routes.")
    minimum = 19 + branches
    if type(max_nodes) is not int or not minimum <= max_nodes <= MAX_NODES:
        raise ValueError(f"Choose {minimum} to {MAX_NODES} graph nodes for {branches} routes; HP variants and Win/Lose count.")
    if type(character_count) is not int or not 2 <= character_count <= MAX_CHARACTERS:
        raise ValueError(f"Choose 2 to {MAX_CHARACTERS} characters, including the player.")
    started = time.perf_counter()
    target, calibrated = reference(difficulty)
    extra = max_nodes - minimum
    layers = (3,) * (extra // 3) + ((extra % 3,) if extra % 3 else ())
    # Fix the canonical duration reference before constructing the candidate.
    ref = build_world(calibrated["level"], calibrated["enemy_hp"], 2, layers)
    world = build_world(calibrated["level"], calibrated["enemy_hp"], branches, layers)
    characters = attach_characters(world, character_count)
    assert len(world["nodes"]) <= max_nodes
    assert {c for n in world["nodes"] for c in n["characters"]} == set(range(character_count))
    epsilon = Q(1, 20)
    assert abs(world["losses"][0] - target) <= epsilon
    assert all(abs(a[0] - b[0]) <= epsilon for a, b in zip(world["table"], ref["table"]))
    document = dict(title="Generated game graph", difficulty=difficulty,
                    branches=branches, target=fraction(target), epsilon=fraction(epsilon),
                    source="Local graph generator", nodes=world["nodes"],
                    profile=dict(dx=HERO_LEVEL, iq=10, weapon="punch"), deterministic_max="9/10",
                    max_nodes=max_nodes, character_count=character_count, characters=characters,
                    horizon=len(world["table"]) - 1,
                    edges=[dict(source=s, target=v, probability=fraction(p), value=float(p))
                           for s, row in enumerate(world["rows"]) for v, p in row.items()],
                    choices=[dict(state=s, actions=[dict(label=label,
                              outcomes=[dict(target=v, probability=fraction(p), value=float(p))
                                        for v, p in row.items()]) for label, row in opts.items()])
                             for s, opts in enumerate(world["choices"])],
                    exact_loss=fraction(world["losses"][0]), loss=float(world["losses"][0]),
                    duration=[dict(t=i, actual=float(row[0]), reference=float(ref["table"][i][0]),
                                   exact=fraction(row[0]), reference_exact=fraction(ref["table"][i][0]))
                              for i, row in enumerate(world["table"])],
                    first_state=0, hp_max=HP_LIMIT, starting_hp=GRID, enemy_level=world["level"],
                    combat_profile="Unarmed 3d6 · ST 10 · Attack / Defend · uniform strategy",
                    computed_seconds=time.perf_counter() - started)
    document["additional"] = additional_checks(world, Q(9,10))
    scenes.attach(world, document)
    document["model_hash"] = hashlib.sha256(json.dumps(document, sort_keys=True).encode()).hexdigest()
    return document, world, ref, combat(world["level"])


def combat_view(level, entry, hero_level=HERO_LEVEL, hero_weapon="punch", enemy_weapon="punch"):
    c = combat(level, hero_level, hero_weapon, enemy_weapon)
    seen, queue = {entry}, deque([entry])
    while queue:
        s = queue.popleft()
        for v in c["rows"][s]:
            if v not in seen:
                seen.add(v)
                queue.append(v)
    return dict(entry=entry,
        nodes=[dict(id=s, a=c["states"][s][0], b=c["states"][s][1],
                    turn=c["states"][s][2], guard=bool(c["states"][s][3]),
                    terminal=c["terminal"][s], lose=c["lose"][s]) for s in sorted(seen)],
        edges=[dict(source=s, target=v, probability=fraction(p), value=float(p))
               for s in sorted(seen) for v, p in c["rows"][s].items()],
        choices=[dict(state=s, actions=[dict(label=label, outcomes=[
            dict(target=v, probability=fraction(p), value=float(p)) for v, p in row.items()])
            for label, row in c["actions"][s].items()]) for s in sorted(seen)],
        loss=fraction(c["exits"][entry][0]), expected_actions=float(c["expectation"][entry]))
