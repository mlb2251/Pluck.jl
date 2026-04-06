# Spawning Design Notes

Despawning is implemented: an object can return `(Despawn)` as its action, which sets its alive flag to `(F)`. Despawned objects are invisible to `occupied` checks and rendered as ghosts.

## Spawning: Open Questions

Spawning is harder because it requires adding new objects to the world mid-simulation. Three approaches considered:

### Option 1: Pre-allocate dormant objects
All objects exist from t=0 but start despawned (alive=F). A "spawner" activates dormant objects by some mechanism.

**Problem:** The dormant object needs to know *when* to wake up. Its `nextlatent` can see all states, so it could watch a specific "spawner" object's latent for a trigger signal. But with multiple dormant projectiles for a single spawner, they need to coordinate which one activates — you don't want all 5 bullets firing at once.

**Possible solution:** Give each dormant object a "slot index" in its latent. The spawner's latent encodes a counter. Dormant object #3 activates when the spawner's counter reaches 3. The spawner increments its counter each time it fires.

**Challenge:** Dormant objects need to identify the spawner in the state list, and currently objects don't have stable identity — they're just positions in a parallel list. You'd need to either hardcode the spawner's index or use position-based lookup.

### Option 2: Spawn action that appends to the world
`nextaction` returns `(Spawn kind lat x y)` and the step function appends a new state.

**Problem:** Breaks the clean zip structure of `step-sts` (kinds and states are parallel lists). The kinds list would also need to grow. Requires changes to the core step loop.

### Option 3: Spawner as a special kind in the step function
After all objects step, a post-pass scans for spawn requests and appends new states.

**Problem:** Similar to Option 2 — needs core loop changes. Also introduces a two-phase step which complicates reasoning.

## Recommendation

Option 1 (pre-allocated dormant objects) is most compatible with the current append-only, stable-index design. The slot-index coordination pattern handles multiple projectiles. Main work needed:
- Convention for dormant objects to find their spawner (e.g. spawner always at a known index, or dormant objects encode the spawner's index in their latent)
- Counter mechanism in spawner's latent (requires nat-valued latent fields, not just bools — may need to generalize Lat)
