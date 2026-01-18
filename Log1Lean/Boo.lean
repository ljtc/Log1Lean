import Mathlib.Tactic

class Est (α : Type) where
  uno : α
  cero : α
  inf : α → α → α
  sup : α → α → α
  comp : α → α
  mi : α → α → Prop
  --
  inf_conm : ∀ x y : α, inf x y = inf y x
  inf_asoc : ∀ x y z : α, inf (inf x y) z = inf x (inf y z)
  inf_idem : ∀ x : α, inf x x = x
  sup_conm : ∀ x y : α, sup x y = sup y x
  sup_asoc : ∀ x y z : α, sup (sup x y) z = sup x (sup y z)
  sup_idem : ∀ x : α, sup x x = x
  abso : ∀ x y : α, sup (inf x y) y = y
  inf_sup : ∀ x y z : α, inf x (sup y z) = sup (inf x y) (inf x z)
  inf_comp : ∀ x : α, inf x (comp x) = cero
  sup_comp : ∀ x : α, sup x (comp x) = uno
  sup_cero : ∀ x : α, sup x cero = x
  inf_uno : ∀ x : α, inf x uno = x
  mi_inf : ∀ x y : α, mi x y ↔ inf x y = x

/- class Boo (B : Type) extends Est B where
  inf_conm : ∀ x y : B, x ⊓ y = y ⊓ x
  inf_asoc : ∀ x y z : B, (x ⊓ y) ⊓ z = x ⊓ (y ⊓ z)
  inf_idem : ∀ x : B, x ⊓ x = x
  sup_conm : ∀ x y : B, x ⊔ y = y ⊔ x
  sup_asoc : ∀ x y z : B, (x ⊔ y) ⊔ z = x ⊔ (y ⊔ z)
  sup_idem : ∀ x : B, x ⊔ x = x
  abso : ∀ x y : B, (x ⊓ y) ⊔ y = y
  inf_sup : ∀ x y z : B, x ⊓ (y ⊔ z) = (x ⊓ y) ⊔ (x ⊓ z)
  inf_comp : ∀ x : B, x ⊓ (x⁻¹) = 𝟘
  sup_comp : ∀ x : B, x ⊔ (x⁻¹) = 𝟙
  sup_cero : ∀ x : B, x ⊔ 𝟘 = x
  inf_uno : ∀ x : B, x ⊓ 𝟙 = x -/

class Copo (α : Type) where
  men : α → α → Prop
  men_ref : ∀ x : α, men x x
  men_tra : ∀ x y z : α, men x y → men y z → men x z
  men_ant : ∀ x y : α, men x y → men y x → x = y

variable (α : Type)

instance : Copo (Set α) where
  men := fun x y ↦ x ∩ y = x
  men_ref := by sorry
  men_tra := by sorry
  men_ant := by sorry
