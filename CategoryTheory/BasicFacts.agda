{-# OPTIONS --cubical --guardedness #-}
module CategoryTheory.BasicFacts where
open import Cubical.Data.Sigma
open import Cubical.Foundations.Univalence
open import Cubical.Data.Sum
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Path
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
open import Cubical.Functions.Embedding
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Isomorphism renaming (isIso to isRealIso ; compIso to compRealIso)
open import Cubical.Foundations.Equiv

open import Cubical.HITs.PropositionalTruncation as PT

open import QuickFixes
open import Cubical.Categories.Category.Base 
open import Cubical.Categories.Category 
open import Cubical.Categories.Functor 
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Adjoint
open import Cubical.Categories.Equivalence.AdjointEquivalence hiding (adjunction)
open import Cubical.Categories.Isomorphism renaming (invIso to CatInvIso)
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Constructions.Opposite
open import Cubical.Tactics.CategorySolver.Reflection

open Category hiding (_∘_)
module isoUniqueness 
  {ℓ ℓ' : Level} {D : Category ℓ ℓ'}
  {x y  : D .ob} {f : D [ x , y ]} {g : D [ y , x ]} 
  (compToId : f ⋆⟨ D ⟩ g ≡ D .id) where
  open isIso
  SectionIsIsoToIsIso : isIso D f → isIso D g 
  SectionIsIsoToIsIso fIso = subst (isIso D) claim (snd invF) where 
    invF = CatInvIso (f , fIso)
    claim : fst invF ≡ g
    claim = fst invF                     ≡⟨ (sym $ D .⋆IdR (fst invF)) ⟩ 
            fst invF ⋆⟨ D ⟩ D .id        ≡⟨ cong (λ h → fst invF ⋆⟨ D ⟩ h) (sym compToId)  ⟩ 
            fst invF ⋆⟨ D ⟩ (f ⋆⟨ D ⟩ g) ≡⟨ sym (D .⋆Assoc (fst invF) f g) ⟩
            (fst invF ⋆⟨ D ⟩ f) ⋆⟨ D ⟩ g ≡⟨ cong (λ h → h ⋆⟨ D ⟩ g) (sec fIso) ⟩
            D .id ⋆⟨ D ⟩ g               ≡⟨ D .⋆IdL g ⟩
            g ∎ 
  RetractionIsIsoToIsIso : isIso D g → isIso D f
  RetractionIsIsoToIsIso gIso = subst (isIso D) claim (snd invG) where
    invG = CatInvIso (g , gIso)
    claim : fst invG ≡ f
    claim = fst invG                     ≡⟨ sym (D .⋆IdL (fst invG)) ⟩
            D . id ⋆⟨ D ⟩ fst invG       ≡⟨ cong (λ h → seq' D h (fst invG)) (sym compToId) ⟩
            (f ⋆⟨ D ⟩ g) ⋆⟨ D ⟩ fst invG ≡⟨ D .⋆Assoc f g (fst invG) ⟩
            f ⋆⟨ D ⟩ (g ⋆⟨ D ⟩ fst invG) ≡⟨ cong (λ h → f ⋆⟨ D ⟩ h) (ret gIso) ⟩
            f ⋆⟨ D ⟩ D .id               ≡⟨ D .⋆IdR f ⟩
            f ∎

module _ {ℓ ℓ' : Level} (C : Category ℓ ℓ') {x y : C .ob} (e : C [ x , y ]) (eIso : isIso C e) {z : C .ob} where
  open isIso
  composeWithIsoLIso : Iso (C [ y , z ]) (C [ x , z ])
  composeWithIsoLIso = iso fun' inv' sec' ret'
    where
    fun' : C [ y , z ] → C [ x , z ]
    fun' f = e ⋆⟨ C ⟩ f
    inv' : C [ x , z ] → C [ y , z ]
    inv' g = inv eIso ⋆⟨ C ⟩ g
    sec' : (g : C [ x , z ]) → fun' (inv' g) ≡ g
    sec' g =
      e ⋆⟨ C ⟩ (inv eIso ⋆⟨ C ⟩ g)
         ≡⟨ (sym $ C .⋆Assoc _ _ _) ⟩
      (e ⋆⟨ C ⟩ inv eIso) ⋆⟨ C ⟩ g
         ≡⟨ cong (λ h → h ⋆⟨ C ⟩ g) (ret eIso) ⟩
      C .id ⋆⟨ C ⟩ g
         ≡⟨ C .⋆IdL g ⟩
      g  ∎
    ret' : (f : C [ y , z ]) → inv' (fun' f) ≡ f
    ret' f =
      inv eIso ⋆⟨ C ⟩ (e ⋆⟨ C ⟩ f)
         ≡⟨ (sym $ C .⋆Assoc _ _ _) ⟩
      (inv eIso ⋆⟨ C ⟩ e) ⋆⟨ C ⟩ f
         ≡⟨ cong (λ h → h ⋆⟨ C ⟩ f) (sec eIso) ⟩
      C .id ⋆⟨ C ⟩ f
         ≡⟨ C .⋆IdL f ⟩
      f  ∎
  composeWithIsoRIso : Iso (C [ z , x ]) (C [ z , y ])
  composeWithIsoRIso = iso fun' inv' sec' ret'
    where
    fun' : C [ z , x ] → C [ z , y ]
    fun' f = f ⋆⟨ C ⟩ e
    inv' : C [ z , y ] → C [ z , x ]
    inv' g = g ⋆⟨ C ⟩ inv eIso
    sec' : (g : C [ z , y ]) → fun' (inv' g) ≡ g
    sec' g =
      g ⋆⟨ C ⟩ inv eIso ⋆⟨ C ⟩ e
        ≡⟨ C .⋆Assoc _ _ _ ⟩
      g ⋆⟨ C ⟩ (inv eIso ⋆⟨ C ⟩ e)
        ≡⟨ cong (λ h → g ⋆⟨ C ⟩ h) (sec eIso) ⟩
      g ⋆⟨ C ⟩ C .id
        ≡⟨ C .⋆IdR g ⟩
      g ∎
    ret' : (f : C [ z , x ]) → inv' (fun' f) ≡ f
    ret' f =
      f ⋆⟨ C ⟩ e ⋆⟨ C ⟩ inv eIso
        ≡⟨ C .⋆Assoc _ _ _ ⟩
      f ⋆⟨ C ⟩ (e ⋆⟨ C ⟩ inv eIso)
        ≡⟨ cong (λ h → f ⋆⟨ C ⟩ h) (ret eIso) ⟩
      f ⋆⟨ C ⟩ C .id
        ≡⟨ C .⋆IdR f ⟩
      f ∎ 

  composeWithIsoLisIso : isRealIso (λ (f : C [ y , z ] ) → e ⋆⟨ C ⟩ f) 
  composeWithIsoLisIso = IsoToIsIso composeWithIsoLIso 

  composeWithIsoRisIso : isRealIso (λ (f : C [ z , x ] ) → f ⋆⟨ C ⟩ e) 
  composeWithIsoRisIso = IsoToIsIso composeWithIsoRIso 
