{-# OPTIONS --cubical --guardedness #-}

module BooleanRing.BooleanRingQuotients.QuotientCase where 

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
open import Cubical.Foundations.HLevels
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
open import Cubical.Algebra.CommRing.Quotient.ImageQuotient
import Cubical.Algebra.CommRing.Quotient.Base as Quot
open import Cubical.Tactics.CommRingSolver

open import Cubical.Algebra.CommRing.Polynomials.Typevariate.UniversalProperty as UP
open import Cubical.Algebra.CommRing.Polynomials.Typevariate.Base
open import WLPO
open import CommRingQuotients.EmptyQuotient
open import CountablyPresentedBooleanRings.PresentedBoole
open import Cubical.Algebra.CommRing.Univalence 

open import CountablyPresentedBooleanRings.Examples.FreeCase
open import Boole.EquivHelper

module equ {ℓ : Level} (A : CommRing ℓ) {X : Type ℓ} (f : X → ⟨ A ⟩) where
  mapsOutOfX : (C : CommRing ℓ) → Type ℓ 
  mapsOutOfX C = X → ⟨ C ⟩ 
  
  transportMap : (B : CommRing ℓ) → (p : A ≡ B) → mapsOutOfX B
  transportMap B = J (λ B p → mapsOutOfX B) f

  transportMap' : (B : CommRing ℓ) → (p : A ≡ B) → mapsOutOfX B
  transportMap' B p = (fst $ fst $ (invEq $ CommRingPath A B) p) ∘ f 

  q : CommRingEquiv A A 
  q = (invEq $ (CommRingPath A A)) refl 

  q=id : fst (fst q) ≡ idfun ⟨ A ⟩ 
  q=id = funExt transportRefl 

  need : (B : CommRing ℓ) → (p : A ≡ B ) → transportMap B p ≡ transportMap' B p 
  need B = J (λ B p → transportMap B p ≡ transportMap' B p) $
    transportMap A refl ≡⟨ transportRefl f ⟩ 
    f ≡⟨⟩ 
    idfun ⟨ A ⟩  ∘ f ≡⟨ cong (λ g → g ∘ f) (sym q=id) ⟩ 
    fst (fst q)  ∘ f ≡⟨⟩ 
    transportMap' A refl ∎ 

  quot : (B : CommRing ℓ) → (p : A ≡ B) → (CommRing ℓ) 
  quot B p = B IQ./Im (transportMap B p)

  equalquot : (B : CommRing ℓ) → (p : A ≡ B) → quot B p ≡ A IQ./Im f
  equalquot B = J (λ B p → quot B p ≡ A IQ./Im f) $ cong (λ g → A IQ./Im g) (transportRefl f)

module expand {γ : binarySequence} {ℓ : Level} (A : BooleanRing ℓ-zero) where
  X = Σ[ n ∈ ℕ ] γ n ≡ true 
  module _ (f : X → ⟨ A ⟩) where 
    open BooleanRingStr ⦃...⦄ 
    instance
      _ = snd A 
    g' : (n : ℕ) → (γn : Dec (γ n ≡ true)) → ⟨ A ⟩
    g' n (yes p) = f (n , p)
    g' n (no ¬p) = 𝟘
    g : ℕ → ⟨ A ⟩
    g n  = g' n (γ n =B true) 
    gYesCase' : (n : ℕ) → (γn : Dec (γ n ≡ true)) → (p : γ n ≡ true) → g' n γn ≡ f ( n , p)
    gYesCase' n (yes _) _ = cong f (Σ≡Prop (λ x → isSetBool _ _) refl)
    gYesCase' n (no ¬p) p = ex-falso $ ¬p p 
    gYesCase : (n : ℕ) → ( p : γ n ≡ true) → g n ≡ f (n , p)
    gYesCase n = gYesCase' n (γ n =B true)
    A/f = A QB./Im f 
    A/g = A QB./Im g
    instance 
      _ = snd A/f
      _ = snd A/g
    open IsCommRingHom (snd $ QB.quotientImageHom {B = A} {f = f} )
    fZeroOnG' : (n : ℕ) → (γn : Dec (γ n ≡ true) ) → QB.quotientImageHom {f = f} $cr g' n γn ≡ 𝟘 
    fZeroOnG' n (yes p) = QB.zeroOnImage (n , p)
    fZeroOnG' n (no ¬p) = pres0 
    fZeroOnG : (n : ℕ) → QB.quotientImageHom {f = f} $cr g n ≡ 𝟘 
    fZeroOnG n = fZeroOnG' n (γ n =B true) 
    A/g→A/f : BoolHom A/g A/f
    A/g→A/f = QB.inducedHom A/f QB.quotientImageHom fZeroOnG
    
    gZeroOnF : (x : X) → QB.quotientImageHom {f = g} $cr f x ≡ 𝟘 
    gZeroOnF x@(n , p) = cong (fst QB.quotientImageHom) (sym $ gYesCase n p) ∙ QB.zeroOnImage n 
    A/f→A/g : BoolHom A/f A/g
    A/f→A/g = QB.inducedHom A/g QB.quotientImageHom gZeroOnF 
    
    A/f→A/g∘qf=qg : A/f→A/g ∘cr (QB.quotientImageHom {f = f}) ≡ QB.quotientImageHom {f = g} 
    A/f→A/g∘qf=qg = QB.evalInduce A/g 

    A/g→A/f∘qg=qf : A/g→A/f ∘cr (QB.quotientImageHom {f = g}) ≡ QB.quotientImageHom {f = f} 
    A/g→A/f∘qg=qf = QB.evalInduce A/f  

    A/g∘q=q : A/f→A/g ∘cr A/g→A/f ∘cr QB.quotientImageHom {f = g} ≡ QB.quotientImageHom {f = g} 
    A/g∘q=q = cong (λ h → A/f→A/g ∘cr h) A/g→A/f∘qg=qf ∙ A/f→A/g∘qf=qg
    A/g=id : A/f→A/g ∘cr A/g→A/f ≡ idCommRingHom (BooleanRing→CommRing A/g)
    A/g=id = CommRingHom≡ $ 
       QB.quotientImageHomEpi (_ , is-set) (cong fst A/g∘q=q) 

    A/f∘q=q : A/g→A/f ∘cr A/f→A/g ∘cr QB.quotientImageHom {f = f} ≡ QB.quotientImageHom {f = f} 
    A/f∘q=q = cong (λ h → A/g→A/f ∘cr h) A/f→A/g∘qf=qg ∙ A/g→A/f∘qg=qf
    A/f=id : A/g→A/f ∘cr A/f→A/g ≡ idCommRingHom (BooleanRing→CommRing A/f)
    A/f=id =  CommRingHom≡ $ 
       QB.quotientImageHomEpi (⟨ A/f ⟩ , is-set) (cong fst A/f∘q=q)

    claim : BooleanRingEquiv A/g A/f
    claim = isoToCommRingEquiv A/g→A/f (fst A/f→A/g) (funExt⁻ $ cong fst A/f=id) (funExt⁻ $ cong fst A/g=id) 

module sum (A : CommRing ℓ-zero) (f g : ℕ → ⟨ A ⟩) where
  -- goal show that ((A / f) / π∘g ) ≡ ((A / g ) / π∘f) ≡ A/f+g
  -- Remark: None of this requires you to use ℕ. You could replace the domains of f , g 
  -- by any type you want
  -- Then I think you could also throw these results into ImageQuotient. 
  f+g : ℕ ⊎ ℕ → ⟨ A ⟩
  f+g = ⊎.rec f g 
  
  A/f : CommRing ℓ-zero
  A/f    = A IQ./Im f 
  opaque
    ginA/f : ℕ → ⟨ A/f ⟩
    ginA/f = (fst $ IQ.quotientImageHom A f) ∘ g

  opaque
    A/f/πg : CommRing ℓ-zero
    A/f/πg = A/f IQ./Im ginA/f
    πg : CommRingHom A/f A/f/πg
    πg = IQ.quotientImageHom A/f ginA/f
  opaque
    πComp : CommRingHom A A/f/πg
    πComp = πg ∘cr IQ.quotientImageHom A f
  open CommRingStr ⦃...⦄
  instance 
    _ = (snd A/f/πg)
  open IsCommRingHom ⦃...⦄
  instance 
    _ = (snd πComp)
  opaque
    unfolding πComp
    unfolding ginA/f
    unfolding πg
    πComp0Ong : (n : ℕ) → πComp $cr (g n) ≡ 0r 
    πComp0Ong n = IQ.zeroOnImage _ _ n
    
    πComp0Onf : (n : ℕ) → πComp $cr (f n) ≡ 0r 
    πComp0Onf n = (cong (fst (IQ.quotientImageHom A/f ginA/f)) 
                  (IQ.zeroOnImage A f n)) ∙ pres0 
  opaque 
    A/f+g : CommRing ℓ-zero
    A/f+g = A IQ./Im f+g
  opaque
    unfolding A/f+g
    sumToComp : CommRingHom A/f+g A/f/πg
    sumToComp = IQ.inducedHom A f+g πComp λ { (inl n) → πComp0Onf n
                                            ; (inr n) → πComp0Ong n } 
  opaque
    unfolding A/f+g
    πSum : CommRingHom A A/f+g
    πSum = IQ.quotientImageHom A f+g 
  instance 
    _ = snd πSum
    _ = snd A/f+g
  opaque
    unfolding πSum
    πSum0Onf : (n : ℕ) → πSum $cr f n ≡ 0r
    πSum0Onf n = IQ.zeroOnImage A f+g (inl n) 
    
    πSum0Ong : (n : ℕ) → πSum $cr g n ≡ 0r
    πSum0Ong n = IQ.zeroOnImage A f+g (inr n)

  -- Epimorphism properties for the quotient maps
  quotientImageHomEpi-A-f+g : {ℓ' : Level} → (S : hSet ℓ') → (f' g' : ⟨ A IQ./Im f+g ⟩ → ⟨ S ⟩) →
                              f' ∘ (IQ.quotientImageHom A f+g) .fst ≡ g' ∘ (IQ.quotientImageHom A f+g).fst → f' ≡ g'
  quotientImageHomEpi-A-f+g = quotientHomEpi A (IQ.genIdeal A f+g)

  quotientImageHomEpi-A-f : {ℓ' : Level} → (S : hSet ℓ') → (f' g' : ⟨ A IQ./Im f ⟩ → ⟨ S ⟩) →
                            f' ∘ (IQ.quotientImageHom A f) .fst ≡ g' ∘ (IQ.quotientImageHom A f).fst → f' ≡ g'
  quotientImageHomEpi-A-f = quotientHomEpi A (IQ.genIdeal A f)

  opaque
    unfolding ginA/f
    unfolding A/f/πg
    quotientImageHomEpi-A/f-ginA/f : {ℓ' : Level} → (S : hSet ℓ') → (f' g' : ⟨ A/f IQ./Im ginA/f ⟩ → ⟨ S ⟩) →
                                     f' ∘ (IQ.quotientImageHom A/f ginA/f) .fst ≡ g' ∘ (IQ.quotientImageHom A/f ginA/f).fst → f' ≡ g'
    quotientImageHomEpi-A/f-ginA/f = quotientHomEpi A/f (IQ.genIdeal A/f ginA/f)

  -- Postulate for evalInduce: inducedHom ∘ quotientImageHom ≡ g
  -- This follows from the eliminator property of SetQuotients but is hard to
  -- prove definitionally due to transport/opaque issues. TODO: prove properly.
  postulate
    evalInduce-A-f+g : {S : CommRing ℓ-zero} {g' : CommRingHom A S}
                       {gfx=0 : ∀ x → g' $cr (f+g x) ≡ CommRingStr.0r (snd S)} →
                       IQ.inducedHom A f+g g' gfx=0 ∘cr IQ.quotientImageHom A f+g ≡ g'
    evalInduce-A-f : {S : CommRing ℓ-zero} {g' : CommRingHom A S}
                     {gfx=0 : ∀ n → g' $cr (f n) ≡ CommRingStr.0r (snd S)} →
                     IQ.inducedHom A f g' gfx=0 ∘cr IQ.quotientImageHom A f ≡ g'
    evalInduce-A/f-ginA/f : {S : CommRing ℓ-zero} {g' : CommRingHom A/f S}
                            {gfx=0 : ∀ n → g' $cr (ginA/f n) ≡ CommRingStr.0r (snd S)} →
                            IQ.inducedHom A/f ginA/f g' gfx=0 ∘cr IQ.quotientImageHom A/f ginA/f ≡ g'

  opaque
    unfolding πSum
    unfolding IQ.inducedHom
    unfolding ginA/f
    compToSumHelper : (n : ℕ) → (IQ.inducedHom A f πSum πSum0Onf) $cr (ginA/f n) ≡ 0r
    compToSumHelper n = πSum0Ong n ∙ pres0

  opaque
    unfolding A/f/πg
    compToSum : CommRingHom A/f/πg A/f+g 
    compToSum = IQ.inducedHom A/f ginA/f (IQ.inducedHom A f πSum πSum0Onf) 
      compToSumHelper
  opaque
    unfolding compToSum
    unfolding πComp
    unfolding sumToComp
    unfolding πSum
    unfolding A/f+g
    unfolding A/f/πg
    unfolding ginA/f
    leftInv∘πSum : (compToSum ∘cr sumToComp) ∘cr πSum ≡ πSum
    leftInv∘πSum =
      (compToSum ∘cr sumToComp) ∘cr πSum
       ≡⟨ CommRingHom≡ refl ⟩
      compToSum ∘cr sumToComp ∘cr πSum
       ≡⟨ cong (λ h → compToSum ∘cr h) $ evalInduce-A-f+g ⟩
      compToSum ∘cr πComp
       ≡⟨ CommRingHom≡ refl ⟩
      (compToSum ∘cr IQ.quotientImageHom A/f _) ∘cr IQ.quotientImageHom A f
       ≡⟨ cong (λ h → h ∘cr IQ.quotientImageHom A f) $ evalInduce-A/f-ginA/f ⟩
      IQ.inducedHom A f πSum πSum0Onf ∘cr IQ.quotientImageHom A f
       ≡⟨ evalInduce-A-f ⟩
      πSum
       ∎     

  opaque
    unfolding sumToComp
    unfolding πSum
    unfolding πComp
    unfolding compToSum
    unfolding A/f+g
    unfolding A/f/πg
    unfolding ginA/f
    rightInv∘πComp : (sumToComp ∘cr compToSum) ∘cr πComp ≡ πComp
    rightInv∘πComp = (sumToComp ∘cr compToSum) ∘cr πComp
                        ≡⟨ CommRingHom≡ refl ⟩
                     sumToComp ∘cr
                     (IQ.inducedHom A/f ginA/f (IQ.inducedHom A f πSum πSum0Onf) compToSumHelper ∘cr ( (IQ.quotientImageHom A/f _)) )
                     ∘cr IQ.quotientImageHom A f
                        ≡⟨ cong (λ h → sumToComp ∘cr h ∘cr IQ.quotientImageHom A f)
                           $ evalInduce-A/f-ginA/f ⟩
                     sumToComp ∘cr (IQ.inducedHom A f πSum πSum0Onf) ∘cr IQ.quotientImageHom A f
                        ≡⟨ CommRingHom≡ refl ⟩
                     sumToComp ∘cr (IQ.inducedHom A f πSum πSum0Onf ∘cr IQ.quotientImageHom A f)
                        ≡⟨ cong (λ h → sumToComp ∘cr h) $ evalInduce-A-f ⟩
                     sumToComp ∘cr πSum
                        ≡⟨ evalInduce-A-f+g ⟩
                     πComp
                        ∎

  opaque 
    leftInv' : (compToSum ∘cr sumToComp) ∘cr πSum ≡ idCommRingHom A/f+g ∘cr πSum
    leftInv' = leftInv∘πSum ∙ (sym $ idCompCommRingHom πSum)
  
  opaque
    unfolding πSum
    unfolding A/f+g
    leftInv : (compToSum ∘cr sumToComp) ≡ idCommRingHom A/f+g
    leftInv = CommRingHom≡ $ quotientImageHomEpi-A-f+g (⟨ A/f+g ⟩ , is-set) _ _ (cong fst leftInv') 
  
  opaque
    unfolding A/f/πg
    unfolding A/f+g
    unfolding πComp
    rightInv' : (sumToComp ∘cr compToSum) ∘cr πComp ≡ idCommRingHom A/f/πg ∘cr πComp
    rightInv' = rightInv∘πComp ∙ (sym $ idCompCommRingHom πComp)
  opaque
    unfolding πComp
    rightInv'' : (((sumToComp ∘cr compToSum) ∘cr πg) ∘cr (IQ.quotientImageHom A f)) ≡ 
                 (idCommRingHom A/f/πg ∘cr πg) ∘cr IQ.quotientImageHom A f
    rightInv'' = (CommRingHom≡ refl) ∙ rightInv' ∙ (CommRingHom≡ refl)
  opaque
    unfolding A/f/πg
    rightInv''' : (sumToComp ∘cr compToSum) ∘cr πg ≡ idCommRingHom A/f/πg ∘cr πg
    rightInv''' = CommRingHom≡ $ quotientImageHomEpi-A-f (⟨ A/f/πg ⟩ , is-set) _ _ (cong fst rightInv'') 
--  opaque 
--    unfolding πg
--    unfolding ginA/f
--    unfolding A/f
--    unfolding A/f/πg
--    unfolding IQ._/Im_
--    unfolding πSum
--    -- Learned fact : unfolding doesn't work for "top-level types", 
--    -- as those can leak out of the definition. 
--    rightInv'''' : (sumToComp ∘cr compToSum) ∘cr πg ≡ 
--                   (idCommRingHom A/f/πg) ∘cr (IQ.quotientImageHom A/f ginA/f)
--    rightInv'''' = ? -- rightInv'''
  opaque
    unfolding πg
    unfolding A/f/πg
    rightInv : sumToComp ∘cr compToSum ≡ idCommRingHom A/f/πg
    rightInv = CommRingHom≡ $ quotientImageHomEpi-A/f-ginA/f (⟨ A/f/πg ⟩ , is-set) _ _ (cong fst rightInv''') 
--    where
--      rightInv'''' : 
--        (sumToComp ∘cr compToSum) ∘cr (IQ.quotientImageHom A/f ginA/f) ≡ 
--        (idCommRingHom A/f/πg)    ∘cr (IQ.quotientImageHom A/f ginA/f)
--      rightInv'''' = rightInv'''
  opaque 
    conclusion : CommRingEquiv A/f+g A/f/πg
    conclusion = isoHomToCommRingEquiv sumToComp compToSum rightInv leftInv 

opaque
  unfolding sum.conclusion
  unfolding sum.A/f/πg
  unfolding sum.A/f+g
  unfolding sum.ginA/f
  quotientConclusion : (A : CommRing ℓ-zero) (f g : ℕ → ⟨ A ⟩) → CommRingEquiv 
    (A IQ./Im (⊎.rec f g)) 
    ((A IQ./Im f) IQ./Im ((fst (IQ.quotientImageHom A f)) ∘ g))
  quotientConclusion A f g = sum.conclusion A f g 

