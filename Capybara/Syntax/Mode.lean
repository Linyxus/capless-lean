namespace Capybara

inductive Mutability : Type where
| readonly : Mutability
| default : Mutability

inductive Mode : Type where
| M : Mutability -> Mode
| drop : Mode


end Capybara
