"""Propose, rebalance and describe live changes using exact rational arithmetic.

A proposal never mutates its input. The server installs it only after Lean has
checked it and after the captured session revision is still current.
"""
import copy
import hashlib
import json
from fractions import Fraction as Q
from functools import lru_cache
import engine
import scenes


def recompute(w, horizon):
    w['rows'] = [engine.uniform_row(opts) for opts in w['choices']]
    w['rank'], w['next'] = engine.path_certificate(w['rows'], w['terminal'])
    # The workshop proposes acyclic adventure graphs. Combat graphs may cycle.
    visiting = set()
    @lru_cache(None)
    def loss(s):
        if w['terminal'][s]:
            return Q(int(w['lose'][s]))
        if s in visiting:
            raise ValueError('This proposal creates an adventure cycle unsupported by the current solver.')
        visiting.add(s)
        result = sum((p * loss(v) for v, p in w['rows'][s].items()), Q(0))
        visiting.remove(s)
        return result
    w['losses'] = [loss(s) for s in range(len(w['rows']))]
    w['table'] = [[Q(int(t)) for t in w['terminal']]]
    for _ in range(horizon):
        old = w['table'][-1]
        w['table'].append([Q(1) if w['terminal'][s] else sum((p*old[v] for v,p in row.items()), Q(0))
                           for s,row in enumerate(w['rows'])])
    return w


def extended_reference(ref, horizon):
    r = copy.deepcopy(ref)
    return recompute(r, horizon)


def remaining_curve(world, ref, current, timestamp, epsilon):
    f = ref['table'][timestamp][0]
    if f == 1:
        raise ValueError('The frozen reference has no surviving mass at this timestamp.')
    values = []
    for k,row in enumerate(world['table']):
        target = (ref['table'][timestamp+k][0]-f)/(1-f)
        if abs(row[current]-target) > epsilon:
            raise ValueError(f'The remaining-duration band fails at event t+{k}.')
        values.append(dict(t=k, actual=float(row[current]), reference=float(target),
                           exact=engine.fraction(row[current]), reference_exact=engine.fraction(target)))
    if Q(values[-1]['exact']) < 1-epsilon or Q(values[-1]['reference_exact']) < 1-epsilon:
        raise ValueError('The infinite tail is not yet certified.')
    return values


def validate(document, world, reference, current, timestamp):
    epsilon = Q(document['epsilon'])
    if len(world['nodes']) > document['max_nodes']:
        raise ValueError('The proposal exceeds the graph node limit.')
    if abs(world['losses'][current] - Q(document['target'])) > epsilon:
        raise ValueError('The remaining defeat probability is outside the fixed difficulty band.')
    for node in world['nodes']:
        if 'combat' in node and abs(Q(node['combat']['lose'])-Q(node['combat'].get('reference_lose',node['combat']['lose']))) > epsilon:
            raise ValueError('A combat leaves its original entry-HP loss band.')
    props = engine.additional_checks(world, Q(document['deterministic_max']))
    duration = remaining_curve(world,reference,current,timestamp,epsilon)
    return props, duration


def document_for(old, world, current, timestamp, props, curve, profile, note):
    d=copy.deepcopy(old)
    d.update(nodes=world['nodes'], profile=profile, first_state=current, timestamp=timestamp,
             exact_loss=engine.fraction(world['losses'][current]), loss=float(world['losses'][current]),
             horizon=len(world['table'])-1, additional=props, duration=curve,
             title='Game graph · rules updated', compensation=note,
             enemy_level=world['level'], combat_profile=f"3d6 · ST/HT 10 · DX {profile['dx']} · {profile['weapon']} · uniform Attack / Defend",
             edges=[dict(source=s,target=v,probability=engine.fraction(p),value=float(p))
                    for s,row in enumerate(world['rows']) for v,p in row.items()],
             choices=[dict(state=s,actions=[dict(label=label,outcomes=[
                       dict(target=v,probability=engine.fraction(p),value=float(p)) for v,p in row.items()])
                       for label,row in opts.items()]) for s,opts in enumerate(world['choices'])])
    scenes.attach(world, d)
    d['model_hash']=hashlib.sha256(json.dumps(d,sort_keys=True).encode()).hexdigest()
    return d


def change_combats(world, duel):
    w=copy.deepcopy(world)
    w['level']=duel['level']
    for n in w['nodes']:
        if 'combat' not in n:
            continue
        s=n['id']; entry=n['combat']['entry']
        # All HP output destinations were retained from the initial full profile.
        destinations=n['combat'].setdefault('destinations', {
            str(w['nodes'][v]['hp']): v for v in w['rows'][s]})
        row={destinations[str(hp)]:p for hp,p in enumerate(duel['exits'][entry]) if p}
        w['choices'][s]={'Resolve combat':row}
        n['combat'].setdefault('reference_lose',n['combat']['lose'])
        n['combat'].update(level=duel['level'],lose=engine.fraction(duel['exits'][entry][0]),
                           expected_actions=float(duel['expectation'][entry]))
    return w


def change_adventure(world, iq):
    w=copy.deepcopy(world)
    for n in w['nodes']:
        if n['scene']!='shrine':
            continue
        targets=set(v for row in w['choices'][n['id']].values() for v in row)
        heal=next(v for v in targets if w['nodes'][v]['scene']=='rest')
        direct=next(v for v in targets if w['nodes'][v]['scene']=='detour')
        w['choices'][n['id']]=engine.recovery_actions(heal,direct,iq)
    return w


def insert_event(world, current, action, destination):
    w=copy.deepcopy(world)
    node=w['nodes'][current]
    if 'combat' in node:
        raise ValueError('Insert events on an ordinary action. Combat exits preserve their full outcome mapping.')
    if action not in w['choices'][current] or destination not in w['choices'][current][action]:
        raise ValueError('Select an existing outcome of an action at the current node.')
    if w['terminal'][destination]:
        raise ValueError('Insert before a live event, not after an output.')
    fresh=len(w['nodes'])
    n=copy.deepcopy(w['nodes'][destination])
    n.pop('combat',None)
    n.update(id=fresh,scene=f'added:{fresh}',kind='event',title=f'Added event {fresh}',
             column=(node['column']+n['column'])/2)
    w['nodes'].append(n)
    p=w['choices'][current][action].pop(destination)
    w['choices'][current][action][fresh]=p
    w['choices'].append({'Continue':{destination:Q(1)}})
    w['terminal'].append(False);w['lose'].append(False)
    return w,fresh


def bypass_neutral_layer(world, destination):
    """Compensate the inserted step by shortening a later neutral layer.
    Never bypass combat, recovery, an output or a character-changing event.
    No node is deleted: identities and previously visited states remain valid.
    """
    w=copy.deepcopy(world)
    if not w['nodes'][destination]['scene'].startswith('event:'):
        return None
    for row in w['choices'][destination].values():
        if any(not w['nodes'][v]['scene'].startswith('event:') for v in row):
            return None
    # Replace each action by its exact two-step outcome law (uniform future choices).
    w['choices'][destination]={label:engine.combine((u,p*q)
        for v,p in row.items() for u,q in engine.uniform_row(w['choices'][v]).items())
        for label,row in w['choices'][destination].items()}
    return w


def propose(snapshot, request):
    if snapshot['fight'] is not None:
        raise ValueError('Finish the current combat before changing rules.')
    current=snapshot['current']; timestamp=snapshot.get('timestamp',0)
    old=copy.deepcopy(snapshot['world']); doc=copy.deepcopy(snapshot['document'])
    scenes.attach(old,doc)
    if old['terminal'][current]:
        raise ValueError('The game has ended. Start a new graph to change its rules.')
    profile=copy.deepcopy(doc.get('profile',dict(dx=12,iq=10,weapon='punch')))
    horizon=len(old['table'])
    ref=extended_reference(snapshot['ref'],timestamp+horizon)
    kind=request.get('kind'); candidates=[]; details={}; changed=copy.deepcopy(profile)
    if kind=='combat':
        dx=request.get('dx');weapon=request.get('weapon')
        if type(dx) is not int or not 8<=dx<=16 or weapon not in engine.WEAPONS:
            raise ValueError('Choose DX 8–16 and one of the listed weapons.')
        changed.update(dx=dx,weapon=weapon)
        if changed==profile:
            raise ValueError('Choose a different combat statistic or weapon.')
        # Try the closest enemy adjustment first; keep hero input exactly as requested.
        levels=sorted(range(6,21),key=lambda n:abs(n-old['level']-(dx-profile['dx'])))
        weapons=list(dict.fromkeys([snapshot['duel']['enemy_weapon'],weapon,'punch','largeKnife','broadsword']))
        for ew in weapons:
            for level in levels:
                duel=engine.combat(level,dx,weapon,ew)
                candidates.append((change_combats(old,duel),duel,
                    f"Player DX {dx}, {weapon}; opponent DX {level}, {ew}. Adventure action laws preserved."))
        details=dict(dx=dx,weapon=weapon)
    elif kind=='adventure':
        iq=request.get('iq')
        if type(iq) is not int or not 2<=iq<=18:
            raise ValueError('Choose adventure IQ 2–18.')
        if iq==profile['iq']:
            raise ValueError('Choose a different adventure statistic.')
        changed['iq']=iq
        candidates=[(change_adventure(old,iq),snapshot['duel'],
            f"IQ {iq}: Careful recovery succeeds with {iq*5}%; Bold recovery is counterbalanced to {100-iq*5}%. Combat unchanged.")]
        details=dict(iq=iq)
    elif kind=='insert':
        action=request.get('action'); destination=request.get('destination')
        if type(destination) is not int:
            raise ValueError('Select an outcome to insert the event on.')
        w,fresh=insert_event(old,current,action,destination)
        scenes.place_inserted(w, fresh, request.get('scene'))
        doc['max_nodes']=max(doc['max_nodes'],len(w['nodes']))
        if doc['max_nodes']>120:
            raise ValueError('This workshop is limited to 120 nodes after live insertions.')
        candidates.append((w,snapshot['duel'],'One new event inserted; all old nodes retained.'))
        compensated=bypass_neutral_layer(w,destination)
        if compensated:
            candidates.append((compensated,snapshot['duel'],
                f"Added event {fresh}; shortened the next neutral event layer after node {destination} to preserve duration."))
        details=dict(action=action,destination=destination,fresh=fresh,source=current,scene=w['nodes'][fresh].get('scene_id'))
    else:
        raise ValueError('Choose combat, adventure or insert.')
    failures=[]
    for w,duel,note in candidates:
        recompute(w,horizon)
        try:
            props,curve=validate(doc,w,ref,current,timestamp)
        except ValueError as exc:
            failures.append(str(exc));continue
        result=document_for(doc,w,current,timestamp,props,curve,changed,note)
        result['change']=dict(kind=kind,details=details,old_profile=profile,timestamp=timestamp,
                             current=current,old_nodes=len(old['nodes']),old_hp=old['nodes'][current]['hp'])
        result['model_hash']=hashlib.sha256(json.dumps(result,sort_keys=True).encode()).hexdigest()
        return result,w,ref,duel
    reason=failures[-1] if failures else 'No candidate.'
    raise ValueError(f'No balanced compensation found among {len(candidates)} candidates. {reason} Current game preserved.')
