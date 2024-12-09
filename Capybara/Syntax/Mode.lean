namespace Capybara

inductive Mutability : Type where
| readonly : Mutability
| default : Mutability

inductive Mode : Type where
| M : Mutability -> Mode
| drop : Mode

notation "ro" => Mode.M Mutability.readonly
notation "ε" => Mode.M Mutability.default
notation "drop" => Mode.drop

end Capybara
