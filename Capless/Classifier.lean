namespace Capless

inductive Classifier : Type where
  | top : Classifier
  | child : Nat -> Classifier -> Classifier

inductive Classifier.Subclass : Classifier -> Classifier -> Prop where
  | id: Subclass a a
  | sub_l : Subclass a b -> Subclass (.child _ a) b

inductive Classifier.Disjoint : Classifier -> Classifier -> Prop where
  | children : (Ne n m) -> Disjoint (child n a) (child m a)
  | sub_l : Disjoint a b -> Disjoint (child _ a) b
  | sub_r : Disjoint a b -> Disjoint a (child _ b)

inductive Kind : Type where
  | classifier : Classifier -> Kind
  | union : Kind -> Kind -> Kind
  | excl : Kind -> Classifier -> Kind

inductive Kind.Disjoint : Kind -> Kind -> Prop where
  | base : Classifier.Disjoint a b -> Disjoint (classifier a) (classifier b)
  | union : Disjoint a b1 -> Disjoint a b2 -> Disjoint a (union b1 b2)
  | excl_this : Classifier.Subclass a b -> Disjoint (excl c b) (classifier a)
  | excl_union : Disjoint a (excl b1 k) -> Disjoint a (excl b2 k) -> Disjoint a (excl (union b1 b2) k)
  | excl : Disjoint a b -> Disjoint a (excl b k)
  | symm : Disjoint a b -> Disjoint b a

inductive Kind.Subkind : Kind -> Kind -> Prop where
  | base : Classifier.Subclass a b -> Subkind (classifier a) (classifier b)
  | union_l : Subkind a1 b -> Subkind a2 b -> Subkind (union a1 a2) b
  | union_r1 : Subkind a b1 -> Subkind a (union b1 b2)
  | union_r2 : Subkind a b2 -> Subkind a (union b1 b2)
  | excl_l : Subkind a b -> Subkind (excl a c) b
  | excl_r : Subkind a b -> Kind.Disjoint a (classifier k) -> Subkind a (excl b k)
  | trans : Subkind a b -> Subkind b c -> Subkind a c

theorem Classifier.subclass_top : Subclass k .top := by
  induction k
  case top => exact .id
  case child n c ih => exact .sub_l ih

theorem Classifier.subclass_of_top : Subclass .top k -> k = .top := by
  intro h
  cases h <;> simp

theorem Classifier.disjoint_symm : Disjoint a b -> Disjoint b a := by
  intro h
  induction h
  case children neq => exact .children (Ne.symm neq)
  case sub_l => constructor; assumption
  case sub_r => constructor; assumption

theorem Classifier.disjoint_top : Disjoint a .top -> False := by
  intro h
  cases h
  . rename_i x a h; exact disjoint_top h

theorem Classifier.subclass_down : Subclass a b -> (a = b) ∨ (∃ n, Subclass a (.child n b)) := by
  intro h
  induction a
  case top => cases h; simp
  case child n p ih =>
    cases h
    case id => simp
    case sub_l l =>
      cases ih l
      . rename_i h1
        right; exists n; rewrite [h1]; constructor
      . rename_i h1
        cases h1
        rename_i w h1
        right; exists w
        apply Subclass.sub_l h1

theorem Classifier.disjoint_up : Disjoint (child n a) b -> Disjoint a b ∨ Subclass b a := by
  intro h
  cases h
  case children ne =>
    right; constructor; constructor
  case sub_l => left; assumption
  case sub_r r =>
    cases disjoint_up r
    . left; apply Disjoint.sub_r; assumption
    . right; apply Subclass.sub_l; assumption

theorem Kind.subkind_refl : Kind.Subkind k k := by
  cases k
  case classifier a =>
    constructor
    constructor
  case union a b =>
    apply Subkind.union_l
    apply Subkind.union_r1
    apply subkind_refl
    apply Subkind.union_r2
    apply subkind_refl
  case excl k a =>
    apply Subkind.excl_r
    apply Subkind.excl_l
    apply subkind_refl
    apply Disjoint.excl_this
    constructor

/- Classifiers fixed for boundary. -/
def Classifier.control := Classifier.child 0 Classifier.top
def Kind.control := Kind.classifier .control
