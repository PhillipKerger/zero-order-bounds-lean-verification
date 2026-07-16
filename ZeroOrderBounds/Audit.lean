import ZeroOrderBounds

/-!
# Axiom audit

Run this module directly to verify the exact axiom dependencies of the public
fixed-horizon lower-bound endpoints.
-/

/--
info: 'ZeroOrderBounds.fixedHorizonLowerBound_strict' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ZeroOrderBounds.fixedHorizonLowerBound_strict

/--
info: 'ZeroOrderBounds.fixedHorizonLowerBound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ZeroOrderBounds.fixedHorizonLowerBound

/--
info: 'ZeroOrderBounds.not_succeedsWithin_advertised' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ZeroOrderBounds.not_succeedsWithin_advertised
