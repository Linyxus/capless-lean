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
inductive LessPermissive : Mutability -> Mutability -> Prop where
| readonly : LessPermissive Mutability.readonly Mutability.default
| refl : LessPermissive m m


end Capybara
