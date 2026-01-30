{-# OPTIONS --cubical --guardedness #-}

module work.Part03 where

-- =============================================================================
-- Part 03: Sequential Limits, Dependent Choice, Markov Principle from SD,
--          and ℕ∞ specific elements
-- =============================================================================

-- Import Part01 and Part02 for base definitions
open import work.Part01 public
open import work.Part02 public

-- Additional imports needed for this part
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (idfun)
open import Cubical.Foundations.Structure using (⟨_⟩)
open import Cubical.Foundations.HLevels using (hProp; isProp⊥; isPropΠ; isSetΣSndProp; isSetΠ)
open import Cubical.Data.Sigma using (Σ≡Prop; _×_)
open import Cubical.Data.Nat renaming (_+_ to _+ℕ_ ; _·_ to _·ℕ_)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Nat.Properties using (discreteℕ)
open import Cubical.Data.Bool hiding (_≤_ ; _≥_) renaming (_≟_ to _=B_)
open import Cubical.Data.Empty renaming (rec to ex-falso)
open import Cubical.Data.Sum
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁; ∣_∣₁; squash₁)
open import Cubical.Relation.Nullary

-- =============================================================================
-- Sequential Limits (Section 11 of work.agda, lines 1497-1565)
-- =============================================================================

-- Sequential limit: compatible sequences in a tower of types
SeqLimit : (E : ℕ → Type ℓ-zero) (p : (n : ℕ) → E (suc n) → E n) → Type ℓ-zero
SeqLimit E p = Σ[ f ∈ ((n : ℕ) → E n) ] ((n : ℕ) → p n (f (suc n)) ≡ f n)

-- Projection from sequential limit to E_0
seqLim-proj₀ : (E : ℕ → Type ℓ-zero) (p : (n : ℕ) → E (suc n) → E n)
             → SeqLimit E p → E 0
seqLim-proj₀ E p (f , _) = f 0

-- Dependent Choice Axiom (from tex):
-- If each p_n is surjective, then seqLim-proj₀ is surjective
DependentChoiceAxiom : Type (ℓ-suc ℓ-zero)
DependentChoiceAxiom = (E : ℕ → Type ℓ-zero) (p : (n : ℕ) → E (suc n) → E n)
  → ((n : ℕ) → (y : E n) → ∥ Σ[ x ∈ E (suc n) ] p n x ≡ y ∥₁)  -- each p_n surjective
  → (e₀ : E 0) → ∥ Σ[ s ∈ SeqLimit E p ] seqLim-proj₀ E p s ≡ e₀ ∥₁

postulate
  dependentChoice-axiom : DependentChoiceAxiom

-- Simpler formulation: Countable Choice
-- Given pointwise truncated existence over ℕ, produce truncated uniform function.
CountableChoiceAxiom : Type (ℓ-suc ℓ-zero)
CountableChoiceAxiom = (A : ℕ → Type ℓ-zero)
  → ((n : ℕ) → ∥ A n ∥₁)
  → ∥ ((n : ℕ) → A n) ∥₁

-- Derive countable choice from dependent choice
countableChoice : CountableChoiceAxiom
countableChoice A witnesses = PT.map extract seqLim-exists
  where
  -- E n is the type of prefix sequences
  E : ℕ → Type ℓ-zero
  E zero = Unit
  E (suc n) = E n × A n

  -- Projection: drop the last element
  p : (n : ℕ) → E (suc n) → E n
  p n (e , _) = e

  -- Each p n is surjective (truncated)
  p-surj : (n : ℕ) → (y : E n) → ∥ Σ[ x ∈ E (suc n) ] p n x ≡ y ∥₁
  p-surj n y = PT.map (λ a → (y , a) , refl) (witnesses n)

  -- E 0 has a canonical element
  e₀ : E 0
  e₀ = tt

  -- Apply dependent choice: get a truncated sequential limit starting at e₀
  seqLim-exists : ∥ Σ[ s ∈ SeqLimit E p ] seqLim-proj₀ E p s ≡ e₀ ∥₁
  seqLim-exists = dependentChoice-axiom E p p-surj e₀

  -- Extract the full sequence from a sequential limit
  extractAt : SeqLimit E p → (n : ℕ) → A n
  extractAt (f , coh) n = snd (f (suc n))

  -- The extracted function
  extract : Σ[ s ∈ SeqLimit E p ] seqLim-proj₀ E p s ≡ e₀ → (n : ℕ) → A n
  extract (s , _) = extractAt s

-- =============================================================================
-- Markov Principle derived from Stone Duality (lines 1566-1592)
-- =============================================================================

-- mp is derived from Stone Duality using the Markov library
-- In work.agda: mp = mp-from-SD sd-axiom
-- Here we postulate it directly since the proof requires infrastructure from work.agda
postulate
  mp : MarkovPrinciple

-- Canonical open proposition: (∃n. α n ≡ true) is open with witness α
someTrueIsOpen : (α : binarySequence) → isOpenProp ((∥ Σ[ n ∈ ℕ ] α n ≡ true ∥₁) , squash₁)
someTrueIsOpen α = α , forward , backward
  where
  forward : ∥ Σ[ n ∈ ℕ ] α n ≡ true ∥₁ → Σ[ n ∈ ℕ ] α n ≡ true
  forward trunc = mp α ¬allFalse
    where
    ¬allFalse : ¬ ((n : ℕ) → α n ≡ false)
    ¬allFalse all-false = PT.rec isProp⊥ (λ { (n , αn=t) → true≢false (sym αn=t ∙ all-false n) }) trunc
  backward : Σ[ n ∈ ℕ ] α n ≡ true → ∥ Σ[ n ∈ ℕ ] α n ≡ true ∥₁
  backward = ∣_∣₁

-- Bundled negation: Closed → Open (requires MP)
¬-Closed : Closed → Open
¬-Closed C = ¬hProp (fst C) , negClosedIsOpen mp (fst C) (snd C)

-- Open propositions are closed under finite disjunction (derived from MP)
openOr : (P Q : hProp ℓ-zero) → isOpenProp P → isOpenProp Q
       → isOpenProp (∥ ⟨ P ⟩ ⊎ ⟨ Q ⟩ ∥₁ , squash₁)
openOr = openOrMP mp

-- =============================================================================
-- Section 11: ℕ_∞ specific elements (lines 1593-1719)
-- =============================================================================

-- The element ∞ : ℕ_∞ (all zeros)
∞ : ℕ∞
∞ = (λ _ → false) , (λ m n αm=t _ → ex-falso (false≢true αm=t))

-- Embedding ℕ into ℕ_∞ (the element that is 1 exactly at position n)
ι : ℕ → ℕ∞
ι n = α , atMostOnce
  where
  α : binarySequence
  α m with discreteℕ m n
  ... | yes _ = true
  ... | no _ = false

  atMostOnce : hitsAtMostOnce α
  atMostOnce m k αm=t αk=t with discreteℕ m n | discreteℕ k n
  ... | yes m=n | yes k=n = m=n ∙ sym k=n
  ... | yes _ | no k≠n = ex-falso (false≢true αk=t)
  ... | no m≠n | yes _ = ex-falso (false≢true αm=t)
  ... | no m≠n | no k≠n = ex-falso (false≢true αm=t)

-- Properties of ι and ∞
ι-at-n : (n : ℕ) → fst (ι n) n ≡ true
ι-at-n n with discreteℕ n n
... | yes _ = refl
... | no n≠n = ex-falso (n≠n refl)

ι-at-m≠n : (n m : ℕ) → ¬ (m ≡ n) → fst (ι n) m ≡ false
ι-at-m≠n n m m≠n with discreteℕ m n
... | yes m=n = ex-falso (m≠n m=n)
... | no _ = refl

-- ι(n) ≠ ∞
ι≠∞ : (n : ℕ) → ¬ (ι n ≡ ∞)
ι≠∞ n ι=∞ = false≢true (sym (cong (λ x → fst x n) ι=∞) ∙ ι-at-n n)

-- ι is injective
ι-injective : (m n : ℕ) → ι m ≡ ι n → m ≡ n
ι-injective m n ιm=ιn =
  let ιm-at-m : fst (ι m) m ≡ true
      ιm-at-m = ι-at-n m
      ιn-at-m : fst (ι n) m ≡ true
      ιn-at-m = cong (λ x → fst x m) (sym ιm=ιn) ∙ ιm-at-m
  in snd (ι n) m n ιn-at-m (ι-at-n n)

-- Markov principle for ℕ∞ elements
ℕ∞-Markov : (α : ℕ∞) → ¬ ((n : ℕ) → fst α n ≡ false) → Σ[ n ∈ ℕ ] fst α n ≡ true
ℕ∞-Markov α = mp (fst α)

-- If α ≠ ∞, then there exists n with αn = true
ℕ∞-notInfty→witness : (α : ℕ∞) → ¬ (α ≡ ∞) → Σ[ n ∈ ℕ ] fst α n ≡ true
ℕ∞-notInfty→witness α α≠∞ = ℕ∞-Markov α ¬all-false
  where
  ¬all-false : ¬ ((n : ℕ) → fst α n ≡ false)
  ¬all-false all-false = α≠∞ (Σ≡Prop isPropHitsAtMostOnce (funExt all-false))

-- The converse: if ∃n. αn = true then α ≠ ∞
witness→ℕ∞-notInfty : (α : ℕ∞) → Σ[ n ∈ ℕ ] fst α n ≡ true → ¬ (α ≡ ∞)
witness→ℕ∞-notInfty α (n , αn=t) α=∞ = false≢true (sym (cong (λ x → fst x n) α=∞) ∙ αn=t)

-- For ℕ∞ elements, the witness is unique
ℕ∞-witness-unique : (α : ℕ∞) → (n m : ℕ) → fst α n ≡ true → fst α m ≡ true → n ≡ m
ℕ∞-witness-unique α n m αn=t αm=t = snd α n m αn=t αm=t

-- α = ∞ ↔ ∀n. αn = false
∞-char : (α : ℕ∞) → (α ≡ ∞) ↔ ((n : ℕ) → fst α n ≡ false)
∞-char α = forward , backward
  where
  forward : α ≡ ∞ → (n : ℕ) → fst α n ≡ false
  forward α=∞ n = cong (λ x → fst x n) α=∞

  backward : ((n : ℕ) → fst α n ≡ false) → α ≡ ∞
  backward all-false = Σ≡Prop isPropHitsAtMostOnce (funExt all-false)

-- Given a witness n, α = ι n
ℕ∞-witness→ι : (α : ℕ∞) → (n : ℕ) → fst α n ≡ true → α ≡ ι n
ℕ∞-witness→ι α n αn=t = Σ≡Prop isPropHitsAtMostOnce (funExt lemma)
  where
  lemma : (m : ℕ) → fst α m ≡ fst (ι n) m
  lemma m with discreteℕ m n
  lemma m | yes m=n = cong (fst α) m=n ∙ αn=t
  lemma m | no m≠n = helper (fst α m) refl
    where
    helper : (b : Bool) → fst α m ≡ b → fst α m ≡ false
    helper false αm=f = αm=f
    helper true αm=t = ex-falso (m≠n (snd α m n αm=t αn=t))

-- Equality in ℕ∞ is closed
ℕ∞-equality-closed : (α β : ℕ∞) → isClosedProp ((α ≡ β) , isSetΣSndProp (isSetΠ (λ _ → isSetBool)) isPropHitsAtMostOnce α β)
ℕ∞-equality-closed α β = γ , forward , backward
  where
  γ : binarySequence
  γ n with fst α n =B fst β n
  ... | yes _ = false
  ... | no _ = true

  forward : α ≡ β → (n : ℕ) → γ n ≡ false
  forward α=β n with fst α n =B fst β n
  ... | yes _ = refl
  ... | no αn≠βn = ex-falso (αn≠βn (cong (λ x → fst x n) α=β))

  backward : ((n : ℕ) → γ n ≡ false) → α ≡ β
  backward all-false = Σ≡Prop isPropHitsAtMostOnce (funExt pointwise)
    where
    pointwise : (n : ℕ) → fst α n ≡ fst β n
    pointwise n with fst α n =B fst β n | all-false n
    ... | yes αn=βn | _ = αn=βn
    ... | no αn≠βn | γn=f = ex-falso (true≢false γn=f)

-- =============================================================================
-- LLPO postulate (required for closedDeMorgan)
-- =============================================================================

postulate
  llpo : LLPO

