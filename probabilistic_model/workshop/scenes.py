"""Spatial membership and its derived graph; never changes game action laws."""
from collections import defaultdict
import copy

PROOF_NAMES = ('scene_membership_exact', 'unique_active_scene', 'outputs_unlocated',
               'scene_graph_exact', 'scene_contents_valid', 'scene_actions_exact')


def default_location(event):
    if event == 'camp':
        return 'camp', 'Camp'
    if event.startswith('event:'):
        # Several decisions, including two consecutive layers, share a place.
        area = int(event.split(':')[1]) // 2
        return f'area:{area}', f'Exploration area {area + 1}'
    if event.startswith('route'):
        return 'crossroads', 'Crossroads'
    if event in ('shrine', 'rest', 'detour'):
        return 'sanctuary', 'Sanctuary'
    if event == 'boss':
        return 'stronghold', 'Stronghold'
    if event == 'treasure':
        return 'vault', 'Treasure vault'
    return event, 'New location'


def attach(world, document):
    """Assign missing locations once; rebuild all derived content and connections.

    `node.scene` is the legacy EVENT key. `node.scene_id` is the new spatial ID.
    IDs are stable through rule changes. No gameplay node or edge is merged.
    """
    registry = {s['id']: copy.deepcopy(s) for s in world.get('scenes', [])}
    items = {i['id']: copy.deepcopy(i) for i in world.get('scene_items', [])}
    by_event = {}
    for n in world['nodes']:
        if world['terminal'][n['id']]:
            if n.get('scene_id') is not None:
                raise ValueError('Terminal outputs must be unlocated.')
            n['scene_id'] = None
            continue
        key, title = default_location(n['scene'])
        sid = n.setdefault('scene_id', key)
        if sid is None:
            raise ValueError('Every playable event needs one scene.')
        if n['scene'] in by_event and by_event[n['scene']] != sid:
            raise ValueError('HP variants of one event must share a scene.')
        by_event[n['scene']] = sid
        if sid not in registry:
            # Scene props reuse ItemKind.reusable with no mechanical effects.
            # Presence alone does not grant a collect/use action.
            item_id = 1000 + len(items)
            items[item_id] = dict(id=item_id, name='Waymarker', kind='reusable')
            registry[sid] = dict(id=sid, title=title, objects=[item_id])
    roster = {c['id'] for c in document['characters']}
    for s in registry.values():
        members = [n for n in world['nodes'] if n['scene_id'] == s['id']]
        s['events'] = list(dict.fromkeys(n['scene'] for n in members))
        s['states'] = [n['id'] for n in members]
        s['characters'] = sorted({c for n in members for c in n['characters'] if c != 0})
        s['column'] = min((n['column'] for n in members), default=0)
        if not set(s['characters']) <= roster or not set(s['objects']) <= items.keys():
            raise ValueError('Scene contents reference an unknown character or item.')
    transitions = defaultdict(list)
    for u, row in enumerate(world['rows']):
        a = world['nodes'][u]['scene_id']
        for v, p in row.items():
            b = world['nodes'][v]['scene_id']
            if p > 0 and a is not None and b is not None and a != b:
                transitions[a, b].append(dict(source=u, target=v))
    world['scenes'] = list(registry.values())
    world['scene_items'] = list(items.values())
    document['nodes'] = world['nodes']
    document['scenes'] = copy.deepcopy(world['scenes'])
    document['scene_items'] = copy.deepcopy(world['scene_items'])
    document['scene_edges'] = [dict(source=a, target=b, witnesses=w)
                               for (a, b), w in sorted(transitions.items())]
    document['scene_model_version'] = 1


def place_inserted(world, fresh, requested=None):
    """Default: destination's scene. A new location is an explicit request."""
    node = world['nodes'][fresh]
    if requested == 'new':
        sid = f'added-scene:{fresh}'
        world.setdefault('scenes', []).append(dict(id=sid, title=f'New scene {fresh}', objects=[]))
        node['scene_id'] = sid
    elif requested is not None:
        if requested not in {s['id'] for s in world.get('scenes', [])}:
            raise ValueError('Choose an existing scene or a new scene.')
        node['scene_id'] = requested


def active_scene(world, current):
    return world['nodes'][current].get('scene_id')
