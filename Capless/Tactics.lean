macro "easy" : tactic => `(tactic| assumption)
macro "split_and" : tactic => `(tactic| repeat any_goals apply And.intro)
macro "apply!" e:term : tactic => `(tactic| apply $e <;> easy)
macro "apply?" e:term : tactic => `(tactic| apply $e <;> try easy)
