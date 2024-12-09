import Capybara.Syntax.Mode
namespace Capybara

inductive CaptureSet : Nat -> Nat -> Type where
| empty : CaptureSet n k
| union : CaptureSet n k -> CaptureSet n k -> CaptureSet n k
| singleton : Fin n -> Mode -> CaptureSet n k
| csingleton : Fin k -> Mode -> CaptureSet n k

end Capybara
