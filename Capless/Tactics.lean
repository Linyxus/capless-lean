/-!
# Useful Tactics

Some funny tactics used in the proofs.
-/

/-- `easy` is an alias of `assumption`. -/
macro "easy" : tactic => `(tactic| assumption)
/-- `split_and` is a tactic that splits all conjunctions in the goal. -/
macro "split_and" : tactic => `(tactic| repeat any_goals apply And.intro)
/-- `apply!` applies a hypothesis and `easy` on all generated subgoals. -/
macro "apply!" e:term : tactic => `(tactic| apply $e <;> easy)
/-- `apply?` applies a hypothesis and try to `easy` on all generated subgoals. -/
macro "apply?" e:term : tactic => `(tactic| apply $e <;> try easy)
