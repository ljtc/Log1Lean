import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic

class GraphicMonoid (M : Type) extends Monoid M where
  graph_id : ∀ a b : M, a * b * a = a * b

variable {M : Type} [GraphicMonoid M]

example {M : Type} [GraphicMonoid M] (a b : M) (h : a * b = 1) : a = 1 := by
  rw [<-one_mul a, <-h, GraphicMonoid.graph_id]
