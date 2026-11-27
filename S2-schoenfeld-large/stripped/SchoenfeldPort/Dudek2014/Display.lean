import Mathlib
import Mathlib
import SchoenfeldPort.Dudek2014.Section22

/-!
P0100 Dudek 2014, Section 2.2, pages 4 to 6: the page 6 display `Display22` derived from the
paper's named analytic inputs, stated as Props:
- `Lemma5`: `Σ Λ(n) w(n) = h - Σ/h + ε(h)` with `|ε(h)| < 48/(5h)`, `Σ` the sum over zeros;
- `SigmaBd`: `|Σ| ≤ |Σ₁| + |Σ₂|` with (7) and the Σ₂ bound at `α = 2`, page 5, both under RH;
- `Schoenfeld`: `0.98 √y < ψ(y) - θ(y) < 1.11 √y + 3 y^{1/3}` for `y ≥ 121`, page 6.
The zero sum `Σ(x, h)` is an abstract function `S`, since the lab has no zeta zeros; the three
Props are exactly the paper's cited steps. With `Theorem2.lean`, Theorem 2 for every `x ≥ 2`
is CONDITIONAL ON these three inputs only.
AI-written Lean code, Claude, 2026-10-19. Checked only by the Lean kernel.
Binary Goldbach is OPEN.
-/

namespace SchoenfeldPort.Dudek2014.Section22
open Real Finset
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

/-- `ψ(y) = Σ_{n ≤ y} Λ(n)`. -/
def psiF (y : ℝ) : ℝ := ∑ n ∈ Iic ⌊y⌋₊, Λ n

end

end SchoenfeldPort.Dudek2014.Section22


