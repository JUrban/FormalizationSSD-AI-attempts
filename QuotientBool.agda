{-# OPTIONS --cubical --guardedness #-}

module QuotientBool where
{- This module restricts the quotients of commutative rings to quotients of Boolean rings -}


open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Functions.Surjection
open import Cubical.Foundations.Function
open import Cubical.Data.Sigma using (Σ≡Prop)

open import Cubical.Algebra.BooleanRing
open import Cubical.Algebra.CommRing

import Cubical.Algebra.CommRing.Quotient.ImageQuotient as IQ
open import Cubical.HITs.SetQuotients 
open import Cubical.Algebra.CommRing.Quotient.Base

module _ {ℓ : Level} (B : BooleanRing ℓ) {X : Type ℓ} (f : X → ⟨ B ⟩) where
  private
    R = BooleanRing→CommRing B
    Q = R IQ./Im f

  open IsCommRingHom
  open CommRingStr ⦃...⦄
  instance
    _ = snd R
    _ = snd Q
  opaque
    quotientPreservesIdem : isIdemRing Q
    quotientPreservesIdem = elimProp
                             {P = λ( y : ⟨ Q ⟩) → y · y ≡ y}
                             (λ y → is-set _ _) $
                             λ r → π r · π r ≡⟨ sym (pres· πHom r r) ⟩
                                   π (r · r) ≡⟨ cong π ( BooleanRingStr.·Idem (snd B) r ) ⟩
                                   π r       ∎
                             where
                               π    : ⟨ R ⟩ → ⟨ Q ⟩
                               π    = fst (quotientHom R (IQ.genIdeal R f) )
                               πHom : IsCommRingHom (snd R) π (snd Q)
                               πHom = snd (quotientHom R (IQ.genIdeal R f))
  opaque 
    _/Im_ : BooleanRing ℓ
    _/Im_ = idemCommRing→BR Q quotientPreservesIdem  

module _ {ℓ : Level} {B : BooleanRing ℓ} {X : Type ℓ} {f : X → ⟨ B ⟩} where
  private
    R = BooleanRing→CommRing B
  opaque
    unfolding _/Im_
    quotientImageHom : BoolHom B (B /Im f)
    quotientImageHom = IQ.quotientImageHom R f
  opaque
    unfolding quotientImageHom

    quotientImageHomSurjective : isSurjection (fst quotientImageHom) 
    quotientImageHomSurjective = quotientHomSurjective (BooleanRing→CommRing B) (IQ.genIdeal (BooleanRing→CommRing B) f) 
   
    quotientImageHomEpi : {ℓ' : Level} → (S : hSet ℓ') → {f' g' : ⟨ B /Im f ⟩ → ⟨ S ⟩} → 
                          f' ∘ quotientImageHom .fst ≡ g' ∘ quotientImageHom .fst → f' ≡ g'
    quotientImageHomEpi S {f'} {g'} = quotientHomEpi (BooleanRing→CommRing B) (IQ.genIdeal (BooleanRing→CommRing B) f) S f' g'
  
    open BooleanRingStr (snd $ B /Im f)
  opaque
    unfolding quotientImageHom
    zeroOnImage : (x : X) → (quotientImageHom $cr (f x)) ≡ 𝟘
    zeroOnImage = IQ.zeroOnImage R f 

  open BooleanRingStr 

  module _ {ℓ' : Level} (S : BooleanRing ℓ') (g : BoolHom B S)
    (gfx=0 : ∀ (x : X) → g $cr (f x) ≡ 𝟘 (snd S)) where
      opaque 
        unfolding _/Im_ 
        unfolding quotientImageHom 
  
        inducedHom : BoolHom (B /Im f) S
        inducedHom = IQ.inducedHom R f g gfx=0 

        inducedHomUnique : (h : BoolHom (B /Im f) S) →
                           (p : g ≡ (h ∘cr quotientImageHom)) →
                           inducedHom ≡ h
        inducedHomUnique = IQ.inducedHomUnique R f g gfx=0
  opaque
    unfolding inducedHom
    unfolding quotientImageHom
    -- The induced homomorphism composed with the quotient map gives back g
    -- This follows from the definition of inducedHom via the eliminator
    evalInduce :
       (S : BooleanRing ℓ) {g : BoolHom B S}
       {gfx=0 : ∀ (x : X) → g $cr (f x) ≡ BooleanRingStr.𝟘 (snd S)} →
       inducedHom S g gfx=0 ∘cr quotientImageHom ≡ g
    evalInduce S {g} {gfx=0} = Σ≡Prop
      (λ h → isPropIsCommRingHom (snd R) h (snd (BooleanRing→CommRing S)))
      refl
