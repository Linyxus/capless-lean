macro "easy" : tactic => `(tactic| assumption)
macro "apply!" e:term : tactic => `(tactic| apply $e <;> easy)
macro "apply?" e:term : tactic => `(tactic| apply $e <;> try easy)
