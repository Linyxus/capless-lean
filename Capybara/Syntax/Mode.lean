namespace Capybara

inductive Mutability : Type where
| readonly : Mutability
| default : Mutability

inductive Mode : Type where
| M : Mutability -> Mode
| drop : Mode

notation "ro" => Mode.M Mutability.readonly
notation "ε" => Mode.M Mutability.default
notation "ε" => Mutability.default
notation "drop" => Mode.drop

/-!
Given `m1` and `m2`, `LessPermissive m1 m2` means that `m1` is less permissive than `m2`.
-/
inductive Mutability.LessPermissive : Mutability -> Mutability -> Prop where
| readonly : LessPermissive Mutability.readonly Mutability.default
| refl : LessPermissive m m

inductive Mode.LessPermissive : Mode -> Mode -> Prop where
| M : Mutability.LessPermissive m1 m2 -> LessPermissive (Mode.M m1) (Mode.M m2)
| drop : LessPermissive m Mode.drop
| refl : LessPermissive m m

end Capybara
