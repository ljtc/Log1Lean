import Mathlib.Tactic

/-
# Álgebras de Boole "desde cero"
-/

class Boo (B : Type) where
  --Estructura:
  uno : B
  cero : B
  inf : B → B → B
  sup : B → B → B
  comp : B → B
  --Axiomas:
  inf_conm : ∀ x y : B, inf x y = inf y x
  inf_asoc : ∀ x y z : B, inf (inf x y) z = inf x (inf y z)
  inf_idem : ∀ x : B, inf x x = x
  sup_conm : ∀ x y : B, sup x y = sup y x
  sup_asoc : ∀ x y z : B, sup (sup x y) z = sup x (sup y z)
  sup_idem : ∀ x : B, sup x x = x
  abso : ∀ x y : B, sup (inf x y) y = y
  inf_sup : ∀ x y z : B, inf x (sup y z) = sup (inf x y) (inf x z)
  inf_comp : ∀ x : B, inf x (comp x) = cero
  sup_comp : ∀ x : B, sup x (comp x) = uno
  sup_cero : ∀ x : B, sup x cero = x
  inf_uno : ∀ x : B, inf x uno = x

--notación
notation "𝟙" => Boo.uno
notation "𝟘" => Boo.cero
infixl:70 "⊓" => Boo.inf
infixl:70 "⊔" => Boo.sup
postfix:max "⁻¹" => Boo.comp

--ejemplo
variable (α : Type)
instance : Boo (Set α) where
  uno := Set.univ
  cero := ∅
  inf := (· ∩ ·)
  sup := (· ∪ ·)
  comp := (·)ᶜ
  inf_conm := Set.inter_comm
  inf_asoc := Set.inter_assoc
  inf_idem := Set.inter_self
  sup_conm := Set.union_comm
  sup_asoc := Set.union_assoc
  sup_idem := Set.union_self
  abso := by
    intro a b; ext x; constructor
    · rintro (⟨xa, xb⟩ | xb)
      assumption'
    · intro xb
      right; assumption
  inf_sup := Set.inter_union_distrib_left
  inf_comp := Set.inter_compl_self
  sup_comp := Set.union_compl_self
  sup_cero := Set.union_empty
  inf_uno := Set.inter_univ

open Boo
variable {B : Type} [Boo B]
variable (x y z : B)

--algunos resultados
theorem inf_cero : x ⊓ 𝟘 = 𝟘 := by
  nth_rw 1 [<-inf_comp x]
  rw [<-inf_asoc, Boo.inf_idem, inf_comp]

theorem sup_uno : x ⊔ 𝟙 = 𝟙 := by
  nth_rw 1 [<-Boo.sup_comp x]
  rw [<-sup_asoc, Boo.sup_idem, sup_comp]

theorem abso₂ : (x ⊔ y) ⊓ y = y := by
  rw [inf_conm, inf_sup, Boo.inf_idem, inf_conm, abso]

theorem sup_inf : x ⊔ (y ⊓ z) = (x ⊔ y) ⊓ (x ⊔ z) := by
  rw [inf_sup]
  nth_rw 3 [sup_conm]
  rw [abso₂]
  nth_rw 2 [inf_conm]
  rw [inf_sup, <-sup_asoc]
  nth_rw 3 [sup_conm]
  rw [abso]
  nth_rw 2 [inf_conm]

theorem comp_un (hci : x ⊓ z = 𝟘) (hbi : x ⊓ y = 𝟘)
    (hcs : x ⊔ z = 𝟙) (hbs : x ⊔ y = 𝟙) : y = z := by
  rw [<-inf_uno y, <-hcs, inf_sup, inf_conm, hbi]
  rw [<-hci,inf_conm, inf_conm y, <-inf_sup, hbs, inf_uno]


#check Boo.inf_comp
--leyes de De Morgan
theorem DM_inf : (x ⊓ y)⁻¹ = x⁻¹ ⊔ y⁻¹ := by
  have co1 : (x ⊓ y) ⊓ (x⁻¹ ⊔ y⁻¹) = cero := by
    rw [inf_asoc, inf_sup, inf_comp, sup_cero]
    rw [inf_conm, inf_asoc, inf_conm x⁻¹]
    rw [inf_comp, inf_cero]
  have co2 : (x ⊓ y) ⊔ (x⁻¹ ⊔ y⁻¹) = 𝟙 := by
    rw [<-sup_asoc, sup_conm (x ⊓ y), sup_inf]
    rw [sup_conm _ x, sup_comp x, inf_conm, inf_uno]
    rw [sup_asoc, sup_comp, sup_uno]
  apply comp_un (x ⊓ y)
  · apply co1
  · apply inf_comp
  · apply co2
  · apply sup_comp

theorem DM_sup : (x ⊔ y)⁻¹ = x⁻¹ ⊓ y⁻¹ := by
  have co_inf : (x ⊔ y) ⊓ (x⁻¹ ⊓ y⁻¹) = 𝟘 := by
    rw [<-inf_asoc, inf_conm (x ⊔ y), inf_sup]
    rw [inf_conm _ x, inf_comp, sup_conm, sup_cero]
    rw [inf_asoc, inf_comp, inf_cero]
  have co_sup : (x ⊔ y) ⊔ (x⁻¹ ⊓ y⁻¹) = 𝟙 := by
    rw [sup_asoc, sup_inf, sup_comp, inf_uno]
    rw [sup_conm, sup_asoc, sup_conm _ x, sup_comp, sup_uno]
  apply comp_un (x ⊔ y)
  · apply co_inf
  · apply inf_comp
  · apply co_sup
  · apply sup_comp

theorem comp_comp : (x⁻¹)⁻¹ = x := by
  apply comp_un x⁻¹
  · rw [inf_conm, inf_comp]
  · rw [inf_comp]
  · rw [sup_conm, sup_comp]
  · rw [sup_comp]


--## Orden

def men : B → B → Prop := fun x y ↦ x ⊓ y = x

--sup a b es un supremo
example : men x (x ⊔ y) := by
  rw [men]
  rw [inf_sup, Boo.inf_idem, sup_conm, inf_conm, abso]


example (ha : men x z) (hb : men y z) : men (x ⊔ y) z := by
  rw [men] at *
  rw [inf_conm, inf_sup, inf_conm, ha, inf_conm, hb]

--inf a b es un ínfimo
example : men (x ⊓ y) x := by
  rw [men, inf_conm,<-inf_asoc, Boo.inf_idem]

example (ha : men z x) (hb : men z y) : men z (x ⊓ y) := by
  rw [men] at *
  rw [<-inf_asoc, ha, hb]

--equivalencias del orden
theorem men_sup : men x y ↔ x ⊔ y = y := by
  rw [men]
  constructor
  · intro h
    rw [<-h, sup_conm, sup_inf, Boo.sup_idem, sup_conm, abso₂]
  · intro h
    rw [<-h, inf_conm, sup_conm, abso₂]

theorem men_comp : men x y ↔ x ⊓ y⁻¹ = 𝟘 := by
  rw [men]
  constructor
  · intro h
    rw [<-h, inf_asoc, inf_comp, inf_cero]
  · intro h
    have hb : y ⊔ (x ⊓ y⁻¹) = y := by
      rw [h, sup_cero]
    rw [sup_inf,sup_comp,inf_uno,sup_conm,<-men_sup,men] at hb
    assumption

--men es un orden parcial
theorem men_refl : men x x := by
  rw [men, Boo.inf_idem]

theorem men_tran (ab : men x y) (bc : men y z) : men x z := by
  rw [men] at *
  rw [<- ab, inf_asoc, bc]

theorem men_anti (ab : men x y) (ba : men y x) : x = y := by
  rw [men] at *
  rw [<-ab, inf_conm]
  assumption

--criterios de igualdad
lemma men_izq (h : ∀ w : B, men x w → men y w) : men y x := by
  specialize h x
  apply h
  apply men_refl

lemma men_der (h : ∀ w, men w x → men w y) : men x y := by
  specialize h x
  apply h
  apply men_refl

theorem ig_izq (h : ∀ w, men x w ↔ men y w) : x = y := by
  have h' := h
  specialize h x
  specialize h' y
  apply men_anti
  · apply h'.2
    apply men_refl
  · apply h.1
    apply men_refl

theorem ig_der (h : ∀ w, men w x ↔ men w y) : x = y := by
  have h' := h
  specialize h x
  specialize h' y
  apply men_anti
  · apply h.1
    apply men_refl
  · apply h'.2
    apply men_refl

lemma men_inf_men (h : men y z) : men (x ⊓ y) (x ⊓ z) := by
  rw [men] at *
  rw [inf_asoc, inf_conm y, inf_asoc, inf_conm z]
  rw [h, <-inf_asoc, Boo.inf_idem]

lemma men_sup_men (h : men y z) : men (x ⊔ y) (x⊔ z) := by
  rw [men_sup] at *
  rw [sup_asoc, sup_conm y, sup_asoc, sup_conm z]
  rw [h, <-sup_asoc, Boo.sup_idem]

lemma men_comp_men (h : men x y) : men y⁻¹ x⁻¹ := by
  rw [men_sup] at h
  rw [men, <-DM_sup, sup_conm, h]

--### Agregar el orden a la estructura de álgebra
class BooOrd (α : Type) extends Boo α where
  mi : α → α → Prop
  mi_def : ∀ u v : α, mi u v ↔ u ⊓ v = u

infixl:50 "≤" => BooOrd.mi


--### Filtros
@[ext]
structure Filtro (α : Type) [BooOrd α] where
  carrier : Set α
  uno_en : 𝟙 ∈ carrier
  inf_en {u v} : u ∈ carrier → v ∈ carrier → u ⊓ v ∈ carrier
  mi_en {u v} : u ∈ carrier → u ≤ v → v ∈ carrier

instance [BooOrd α] : SetLike (Filtro α) α where
  coe := Filtro.carrier
  coe_injective' _ _ := Filtro.ext

--intersección de dos filtro es filtro
instance [BooOrd α] : Min (Filtro α) :=
  ⟨fun F₁ F₂ ↦
    {carrier := F₁ ∩ F₂
     uno_en := ⟨F₁.uno_en, F₂.uno_en⟩
     inf_en := fun ⟨hu, hu'⟩ ⟨hv, hv'⟩ ↦ ⟨F₁.inf_en hu hv, F₂.inf_en hu' hv'⟩
     mi_en := fun ⟨hu, hu'⟩ h ↦ ⟨F₁.mi_en hu h, F₂.mi_en hu' h⟩
  }⟩



--## Morfismos

@[ext]
class HomBoo (F : Type) (A B : outParam Type) [Boo A] [Boo B] where
  toFun : F → A → B
  pre_inf : ∀ (f : F) (a₁ a₂ : A), toFun f (a₁ ⊓ a₂) = (toFun f a₁) ⊓ (toFun f a₂)
  pre_sup : ∀ (f : F) (a₁ a₂ : A), toFun f (a₁ ⊔ a₂) = (toFun f a₁) ⊔ (toFun f a₂)
  pre_comp : ∀ (f : F) (a₁ : A), toFun f (a₁⁻¹) = (toFun f a₁)⁻¹

instance [Boo A] [Boo B] [HomBoo F A B] : CoeFun F (fun _ ↦ A → B) where
  coe := HomBoo.toFun

attribute [coe] HomBoo.toFun


variable {A F G : Type} [Boo A] [HomBoo F A B] [HomBoo G B A]
variable (f : F) (g g' : G)
variable (a a1 a2 : A) (b : B)

open HomBoo

example : f 𝟙 = 𝟙 := by
  rw [<-sup_comp a, pre_sup, pre_comp, sup_comp]

example : f 𝟘 = 𝟘 := by
  rw [<-inf_comp a, pre_inf, pre_comp, inf_comp]

example (h : men a1 a2) : men (f a1) (f a2) := by
  rw [men] at *
  rw [<-pre_inf, h]

def adj : F → G → Prop :=
  fun f g ↦ ∀ (a : A) (b : B), men (f a) b ↔ men a (g b)

#print adj

example (h1 : adj f g) (h2 : adj f g') : toFun g = toFun g' := by
  rw [adj] at *
  funext z
  apply ig_der
  intro w
  specialize h1 w z
  specialize h2 w z
  rw [<-h1, <-h2]
