/-
Copyright (c) 2025 Naïm Favier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naïm Favier
-/
import Mathlib.CategoryTheory.Iso
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-!
# Tensorial strengths and strong endofunctors

A (left) tensorial strength for an endofunctor `F` on a monoidal category `C` is
a natural transformation `σ X Y : X ⊗ F.obj Y ⟶ F.obj (X ⊗ Y)`.
There is a corresponding notion of *right* strength, and a functor is called **strong**
if it is equipped with both a left and a right strength.
Additionally, in a symmetric monoidal category we can require the
left and right strengths to be related by the braiding. In that case, we say that `F`
is a **symmetric** strong endofunctor.
-/

universe u₁ v₁

namespace CategoryTheory

open Category Functor MonoidalCategory

variable
  {C : Type u₁} [Category.{v₁} C] [MonoidalCategory.{v₁} C]
  (F : C ⥤ C)

class LeftStrong where
  σ : ∀ X Y : C, X ⊗ F.obj Y ⟶ F.obj (X ⊗ Y)
  σ_natural_left :
    ∀ {X Y : C} (f : X ⟶ Y) (X' : C),
      f ▷ F.obj X' ≫ σ Y X' = σ X X' ≫ F.map (f ▷ X') := by
    aesop_cat
  σ_natural_right :
    ∀ {X Y : C} (X' : C) (f : X ⟶ Y) ,
      X' ◁ F.map f ≫ σ X' Y = σ X' X ≫ F.map (X' ◁ f) := by
    aesop_cat
  σ_associativity :
    ∀ X Y Z : C,
      σ (X ⊗ Y) Z ≫ F.map (α_ X Y Z).hom =
        (α_ X Y (F.obj Z)).hom ≫ X ◁ σ Y Z ≫ σ X (Y ⊗ Z) := by
    aesop_cat
  σ_unitality :
    ∀ X : C,
      σ (𝟙_ C) X ≫ F.map (λ_ X).hom =
        (λ_ (F.obj X)).hom := by
    aesop_cat

namespace LeftStrong

attribute [reassoc (attr := simp)] σ_natural_left σ_natural_right σ_associativity σ_unitality

end LeftStrong

class RightStrong where
  τ : ∀ X Y : C, F.obj X ⊗ Y ⟶ F.obj (X ⊗ Y)
  τ_natural_left :
    ∀ {X Y : C} (f : X ⟶ Y) (X' : C),
      F.map f ▷ X' ≫ τ Y X' = τ X X' ≫ F.map (f ▷ X') := by
    aesop_cat
  τ_natural_right :
    ∀ {X Y : C} (X' : C) (f : X ⟶ Y) ,
      F.obj X' ◁ f ≫ τ X' Y = τ X' X ≫ F.map (X' ◁ f) := by
    aesop_cat
  τ_associativity :
    ∀ X Y Z : C,
      τ X (Y ⊗ Z) ≫ F.map (α_ X Y Z).inv =
        (α_ (F.obj X) Y Z).inv ≫ τ X Y ▷ Z ≫ τ (X ⊗ Y) Z := by
    aesop_cat
  τ_unitality :
    ∀ X : C,
      τ X (𝟙_ C) ≫ F.map (ρ_ X).hom =
        (ρ_ (F.obj X)).hom := by
    aesop_cat

namespace RightStrong

attribute [reassoc (attr := simp)] τ_natural_left τ_natural_right τ_associativity τ_unitality

/-- Alternative form of associativity for right strengths, similar to
the one for left strengths. -/
@[reassoc (attr := simp)]
lemma τ_associativity' [RightStrong F] (X Y Z : C) :
    (α_ (F.obj X) Y Z).hom ≫ τ X (Y ⊗ Z) =
      τ X Y ▷ Z ≫ τ _ Z ≫ F.map (α_ X Y Z).hom := by
  apply (α_ (F.obj X) Y Z).eq_inv_comp.1
  rw [← assoc, ← assoc]
  apply (F.mapIso (α_ X Y Z)).comp_inv_eq.1
  simp

end RightStrong

open LeftStrong RightStrong

class Strong extends LeftStrong F, RightStrong F where
  strengths_associativity :
    ∀ X Y Z : C,
      σ X Y ▷ Z ≫ τ (X ⊗ Y) Z ≫ F.map (α_ X Y Z).hom =
        (α_ X (F.obj Y) Z).hom ≫ X ◁ τ Y Z ≫ σ X (Y ⊗ Z) := by
    aesop_cat

namespace Strong

attribute [reassoc (attr := simp)] strengths_associativity

end Strong

variable [SymmetricCategory C]

class SymmetricStrong extends Strong F where
  strengths_symmetric :
    ∀ X Y : C,
      (β_ X (F.obj Y)).hom ≫ τ Y X = σ X Y ≫ F.map (β_ X Y).hom := by
    aesop_cat

namespace SymmetricStrong

attribute [reassoc] strengths_symmetric

variable [SymmetricStrong F]

@[reassoc (attr := simp)]
lemma strengths_symmetric' (X Y : C) :
  (β_ (F.obj X) Y).hom ≫ σ Y X = τ X Y ≫ F.map (β_ X Y).hom := by
  apply (β_ (F.obj X) Y).eq_inv_comp.1
  rw [← SymmetricCategory.braiding_swap_eq_inv_braiding]
  rw [strengths_symmetric_assoc]
  rw [← F.map_comp]
  simp

end SymmetricStrong

end CategoryTheory
