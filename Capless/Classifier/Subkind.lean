import Capless.Classifier.Subtract

namespace Capless

/-- `K` is a subkind of `L` if every node in `K` is present in `L`. -/
inductive Kind.Subkind : Kind -> Kind -> Prop where
  | subtract : Subtract K1 K2 R -> IsEmpty R -> Subkind K1 K2

theorem Kind.Subkind.empty_r_inv (hs : Subkind K1 K2) (he : IsEmpty K2) : IsEmpty K1 := by
  cases hs
  apply! Subtract.empty_r_inv


end Capless
