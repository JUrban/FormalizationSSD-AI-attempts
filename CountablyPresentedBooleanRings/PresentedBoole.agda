{-# OPTIONS --cubical --guardedness #-}
module CountablyPresentedBooleanRings.PresentedBoole where 

open import Cubical.Data.Sigma
open import Cubical.Data.Sum
import Cubical.Data.Sum as ⊎
open import Cubical.Data.Bool hiding ( _≤_ ; _≥_ ) renaming ( _≟_ to _=B_)
open import Cubical.Data.Empty renaming (rec to ex-falso ; rec* to empty-func)
open import Cubical.Data.Nat renaming (_+_ to _+ℕ_ ; _·_ to _·ℕ_)
open import Cubical.Data.Nat.Order 
open <-Reasoning
open import Cubical.Data.Nat.Bijections.Sum

open import Cubical.Foundations.Structure
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Functions.Surjection
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.BooleanRing
open import Cubical.Algebra.BooleanRing.Initial
open import Cubical.Algebra.BooleanRing.Instances.Bool
open import Cubical.Algebra.CommRing.Instances.Bool
open import Cubical.Relation.Nullary

open import Cubical.HITs.PropositionalTruncation as PT

open  import BooleanRing.FreeBooleanRing.FreeBool
import BooleanRing.FreeBooleanRing.FreeBool as FB

open  import BooleanRing.FreeBooleanRing.SurjectiveTerms
open  import BooleanRing.FreeBooleanRing.freeBATerms

open import QuotientBool as QB
import Cubical.HITs.SetQuotients as SQ
import Cubical.Algebra.CommRing.Quotient.ImageQuotient as IQ
open import Cubical.Algebra.CommRing.Ideal
import Cubical.Algebra.CommRing.Kernel as CK
open import Cubical.Algebra.Ring.Kernel as RK
open import Cubical.Algebra.CommRing.Quotient.Base
import Cubical.Algebra.CommRing.Quotient.Base as Quot
open import Cubical.Tactics.CommRingSolver

open import Cubical.Algebra.CommRing.Polynomials.Typevariate.UniversalProperty as UP
open import Cubical.Algebra.CommRing.Polynomials.Typevariate.Base
open import WLPO
open import CommRingQuotients.EmptyQuotient
open import Boole.Shouldhave
open import BooleanRing.BoolRingUnivalence

{- I freeA'≃freeA to define what is a countably presented BA before I can define what a Stone space is.
--
-- I think I want it to be a predicate on Boolean rings. If so, the following quotHom be examples:
--
-- BoolBR
-- freeBA ℕ 
-- the Boolean algebra underlying ℕ-infty. 
--
-- So far, I've shown the first two are quotients of freeBA ℕ by some function from ℕ. 
-- This definition carries the benefit that it's of type-level ℓ-zero. 
-- (which should be the case as our work should work independently from universes. 
--} 

module _ {ℓ ℓ' : Level} (A : BooleanRing ℓ) (B : BooleanRing ℓ') where
  BooleanRingEquiv : Type (ℓ-max ℓ ℓ')
  BooleanRingEquiv = BoolRingEquiv A B 

isPropIsBoolRingHom : {ℓ ℓ' : Level} → {A : Type ℓ} {B : Type ℓ'} (R : BooleanRingStr A) (f : A → B) (S : BooleanRingStr B)
  → isProp (IsBoolRingHom R f S)
isPropIsBoolRingHom R f S = isPropIsCommRingHom (BooleanRingStr→CommRingStr R) f (BooleanRingStr→CommRingStr S) 
  
module _ { ℓ ℓ' : Level} (B : BooleanRing ℓ) (C : BooleanRing ℓ') (f g : BooleanRingEquiv B C) where
  BooleanRingEquiv≡ : (fst (fst f) ≡ fst (fst g)) → f ≡ g
  BooleanRingEquiv≡ p = Σ≡Prop (λ h → isPropIsBoolRingHom (snd B) (fst h) (snd C)) 
                        (Σ≡Prop isPropIsEquiv p) 

module _ {ℓ : Level} (B : BooleanRing ℓ) where
  open IsCommRingHom 
  idBoolHom : BoolHom B B
  idBoolHom .fst = idfun ⟨ B ⟩
  idBoolHom .snd .pres0     = refl
  idBoolHom .snd .pres1     = refl
  idBoolHom .snd .pres+ a b = refl
  idBoolHom .snd .pres· a b = refl
  idBoolHom .snd .pres- a   = refl 

  idFunGivesIdBoolHom : (f : BoolHom B B) → (fst f ≡ idfun ⟨ B ⟩) → f ≡ idBoolHom
  idFunGivesIdBoolHom f p = CommRingHom≡ p

  idBoolEquiv : BooleanRingEquiv B B
  idBoolEquiv .fst .fst = idfun ⟨ B ⟩
  idBoolEquiv .fst .snd = idIsEquiv ⟨ B ⟩ 
  idBoolEquiv .snd = snd idBoolHom 

  idFunGivesIdBoolEquiv : (f : BooleanRingEquiv B B ) → (fst (fst f) ≡ idfun ⟨ B ⟩) → f ≡ idBoolEquiv
  idFunGivesIdBoolEquiv f = BooleanRingEquiv≡ B B f idBoolEquiv 

module _ {ℓ ℓ' : Level} (A : BooleanRing ℓ) (B : BooleanRing ℓ') (f : BooleanRingEquiv A B) where
  invBooleanRingEquiv : BooleanRingEquiv B A
  invBooleanRingEquiv = invCommRingEquiv (BooleanRing→CommRing A) (BooleanRing→CommRing B) f

  BooleanEquivToHom : BoolHom A B
  BooleanEquivToHom = fst (fst f) , snd f 

  BooleanEquivToHomInv : BoolHom B A
  BooleanEquivToHomInv = fst (fst invBooleanRingEquiv) , snd invBooleanRingEquiv 

  BooleanEquivLeftInv : BooleanEquivToHomInv ∘cr BooleanEquivToHom ≡ idBoolHom A
  BooleanEquivLeftInv = idFunGivesIdBoolHom A (BooleanEquivToHomInv ∘cr BooleanEquivToHom)
     (funExt $ Iso.ret (equivToIso (fst f)))

  BooleanEquivRightInv : BooleanEquivToHom ∘cr BooleanEquivToHomInv ≡ idBoolHom B
  BooleanEquivRightInv = idFunGivesIdBoolHom B (BooleanEquivToHom ∘cr BooleanEquivToHomInv)
     (funExt $ Iso.sec (equivToIso (fst f))) 

_is-presented-by_/_ : {ℓ : Level} → (B : BooleanRing ℓ) → 
  (A : Type ℓ) → {X : Type ℓ} → (f : X → ⟨ freeBA A ⟩) → Type ℓ 
B is-presented-by A / f = BooleanRingEquiv B (freeBA A /Im f)

has-Countability-structure : {ℓ : Level} → (A : Type ℓ) → Type ℓ
has-Countability-structure A = Σ[ α ∈ binarySequence ] Iso A (Σ[ n ∈ ℕ ] α n ≡ true)

countℕ : has-Countability-structure ℕ
countℕ .fst _ = true
countℕ .snd = iso fun' inv' sec' ret'
  where
  fun' : ℕ → Σ[ n ∈ ℕ ] true ≡ true
  fun' n = n , refl
  inv' : Σ[ n ∈ ℕ ] true ≡ true → ℕ
  inv' (n , _) = n
  sec' : (b : Σ[ n ∈ ℕ ] true ≡ true) → fun' (inv' b) ≡ b
  sec' b = Σ≡Prop (λ _ → isSetBool _ _) refl
  ret' : (n : ℕ) → inv' (fun' n) ≡ n
  ret' n = refl 

has-Boole-ω : (B : BooleanRing ℓ-zero) → Type (ℓ-suc ℓ-zero) 
has-Boole-ω B = Σ[ A ∈ Type ] ( (has-Countability-structure A) × 
              (Σ[ X ∈ Type ] ( (has-Countability-structure X) ×
              (Σ[ f ∈ (X → ⟨ freeBA A ⟩) ] B is-presented-by A /( f)))))

has-Boole-ω' : (B : BooleanRing ℓ-zero) → Type ℓ-zero 
has-Boole-ω' B = Σ[ f ∈ (ℕ → ⟨ freeBA ℕ ⟩) ] (B is-presented-by ℕ / f)

has-Boole'→ : (B : BooleanRing ℓ-zero) → has-Boole-ω' B → has-Boole-ω B
has-Boole'→ B x = ℕ , countℕ , ℕ , countℕ , x


