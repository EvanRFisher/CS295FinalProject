open import Data.Rational as ℚmod renaming (_+_ to _+ℚ_) renaming (_-_ to _-ℚ_) renaming (_*_ to _*ℚ_) renaming (_>_ to _>ℚ_) renaming (_<_ to _<ℚ_) renaming (_≤_ to _≤ℚ_)
import Data.Rational
open import Data.Nat renaming (_>_ to _>ᴺ_ ) renaming (_<_ to _<ᴺ_ ) renaming (_≤_ to _≤ᴺ_ ) renaming (suc to Sᴺ) renaming (_*_ to _*ᴺ_) renaming (_+_ to _+ᴺ_)
open import Data.Integer renaming (_*_ to _*ᶻ_)  renaming (suc to Sᶻ) renaming (-_ to -ᶻ_)
open import Data.Rational.Properties as ℚprop
open import Data.Integer.Properties as ℤprop
open import Data.Nat.Properties as ℕprop
open import Relation.Nullary
open import Agda.Builtin.Equality
open import Relation.Binary.PropositionalEquality
open import Axiom.Extensionality.Propositional as Extensionality

-- Not used. Sometimes, Signs show up in targets, and renaming Data.Sign.Base.* to *Sign makes them more readable.
open import Data.Sign.Base renaming (_*_ to _*Sign_)



-- Definitions
infix 5 _∨_
data _∨_ (A B : Set) : Set where --From IC12
  Inl : A → A ∨ B
  Inr : B → A ∨ B

--abs
abs : ℚ → ℚ
abs (mkℚ (+_ n) denom-1 cop) = mkℚ (+_ n) denom-1 cop -- Abs n = n if n>=0
abs (mkℚ (-[1+_] n) denom-1 cop) = mkℚ (+_ (Sᴺ n)) denom-1 cop -- Abs -(1+a)/b = (a+1)/b if a<0

data ℝ : Set where
 --⟪sequence,epsilon to number,proof⟫
    ⟪_,_,_⟫ : (f   : ( ℕ → ℚ )) →
              (ε→n : (ℚ → ℕ )) →
              (∀(ε : ℚ) → ∀(a b : ℕ)
                → ε >ℚ 0ℚ
                → a >ᴺ (ε→n ε)
                → b >ᴺ (ε→n ε)
                → abs (f a -ℚ f b) ≤ℚ ε ) → ℝ
                -- Real numbers are represented by cauchy sequences
                -- And are thus a pair of a function f: ℕ → ℚ
                -- And a proof that ∀(ε : ℚ). ∃ (n : ℕ). ∀(a,b : ℕ).
                --                             a>n ∧ b>n → ∣ f(a) - f(b) ∣ < ε

f←_ : ℝ → (ℕ → ℚ)
f← ⟪ f , ε→n , x ⟫ = f

infix 4 _≃ʳ_
data _≃ʳ_ : ℝ → ℝ → Set where
    *≡* : ∀ {p q : ℝ} → (ε→n : (ℚ → ℕ )) → (∀(ε : ℚ) → ∀(a : ℕ) → ε >ℚ 0ℚ → a >ᴺ (ε→n ε) → abs ((f← p) a -ℚ (f← q) a) ≤ℚ ε ) → p ≃ʳ q
-- If ∀ε,∃N such that the two sequences are always less than ε apart for all indexes > N, the two converge to the same value and are equal.



const : (x : ℚ) → (ℕ → ℚ) --Creates a constant function
const x = λ _ → x

const-inv : ∀ (x : ℚ) → ∀ (n : ℕ) → const x n ≡ x
const-inv = λ x n → refl

--Postulates

-- Some interactions of rational operations and comparison not included in the standard library, as well as some properties of abs.
-- Unnormalized natural numbers, while somewhat easier to work with, have less support, so most properties are postulated here.
postulate
    sum[≤] : ∀{a b c d : ℚ} → a ≤ℚ c → b ≤ℚ d → a +ℚ b ≤ℚ c +ℚ d
    abs-split[+/≤] : ∀(a b : ℚ) → abs(a +ℚ b) ≤ℚ abs (a) +ℚ abs(b)
    split[½/+] : ∀ (a : ℚ) → (½ *ℚ a) +ℚ (½ *ℚ a) ≡ a

--Proof is slightly messier to have c on the right.
linear[<ᴺ/+] : ∀ (a b c : ℕ) → a <ᴺ b → a <ᴺ b +ᴺ c
linear[<ᴺ/+] a b zero a<b rewrite ℕprop.+-identityʳ b = a<b
linear[<ᴺ/+] a b (Sᴺ c) a<b with ℕprop.≤-step (linear[<ᴺ/+] a b c a<b)
... | prf rewrite +-suc b c = prf

relim[+/<ᴺ] : ∀ (a b c : ℕ) → a +ᴺ b <ᴺ c → a <ᴺ c
relim[+/<ᴺ] a zero c ab<c rewrite ℕprop.+-identityʳ a = ab<c
relim[+/<ᴺ] a (Sᴺ b) (Sᴺ c) (s≤s ab<c) with relim[+/<ᴺ] a b (Sᴺ c)
... | prf rewrite +-suc a b = prf (ℕprop.≤-step ab<c)

lelim[+/<ᴺ] : ∀ (a b c : ℕ) → a +ᴺ b <ᴺ c → b <ᴺ c
lelim[+/<ᴺ] zero b c ab<c = ab<c
lelim[+/<ᴺ] (Sᴺ a) b (Sᴺ c) (s≤s ab<c) with lelim[+/<ᴺ] a b (Sᴺ c)
... | prf rewrite +-suc a b = prf (ℕprop.≤-step ab<c)

-- Properties of ≤ and < over ℚ. Adjusted from agda basics-002
postulate
    xRx[≤] : ∀ (m : ℚ) → m ≤ℚ m
    _⊚[≤]_ : ∀ {m n p : ℚ} → n ≤ℚ p → m ≤ℚ n → m ≤ℚ p
    _⋈[≤]_ : ∀ {m n : ℚ} → m ≤ℚ n → n ≤ℚ m → m ≡ n
    _⊚[<]_ : ∀ {m n p : ℚ} → n <ℚ p → m <ℚ n → m <ℚ p
    _⊚[</≤]_ : ∀ {m n p : ℚ} → n <ℚ p → m ≤ℚ n → m <ℚ p
    _⊚[≤/<]_ : ∀ {m n p : ℚ} → n ≤ℚ p → m <ℚ n → m <ℚ p
    lmono[+/≤] : ∀ (x x′ y : ℚ) → x ≤ℚ x′ → x +ℚ y ≤ℚ x′ +ℚ y
    rmono[+/≤] : ∀ (x y y′ : ℚ) → y ≤ℚ y′ → x +ℚ y ≤ℚ x +ℚ y′
    lmono[+/<] : ∀ (x x′ y : ℚ) → x <ℚ x′ → x +ℚ y <ℚ x′ +ℚ y
    rmono[+/<] : ∀ (x y y′ : ℚ) → y <ℚ y′ → x +ℚ y <ℚ x +ℚ y′

    lmono[*/<] : ∀ (x y y′ : ℚ) → y <ℚ y′ → 0ℚ <ℚ x → x *ℚ y <ℚ x *ℚ y′

-- Properties of + and * over ℚ. Adjusted from agda basics-002
postulate
    lunit[+] : ∀ (m : ℚ) → 0ℚ +ℚ m ≡ m
    runit[+] : ∀ (m : ℚ) → m +ℚ 0ℚ ≡ m
    assoc[+] : ∀ (m n p : ℚ) → m +ℚ (n +ℚ p) ≡ (m +ℚ n) +ℚ p
    commu[+] : ∀ (m n : ℚ) → m +ℚ n ≡ n +ℚ m
    lunit[×] : ∀ (m : ℚ) → 1ℚ *ℚ m ≡ m
    runit[×] : ∀ (m : ℚ) → m *ℚ 1ℚ ≡ m
    lzero[×] : ∀ (m : ℚ) → 0ℚ *ℚ m ≡ 0ℚ
    rzero[×] : ∀ (m : ℚ) → m *ℚ 0ℚ ≡ 0ℚ
    assoc[×] : ∀ (m n p : ℚ) → m *ℚ (n *ℚ p) ≡ (m *ℚ n) *ℚ p
    commu[×] : ∀ (m n : ℚ) → m *ℚ n ≡ n *ℚ m
    ldist[×] : ∀ (m n p : ℚ) → m *ℚ (n +ℚ p) ≡ m *ℚ n +ℚ m *ℚ p
    rdist[×] : ∀ (m n p : ℚ) → (m +ℚ n) *ℚ p ≡ m *ℚ p +ℚ n *ℚ p
    distr[-] : ∀ (m n p : ℚ) → m -ℚ (n +ℚ p) ≡ m -ℚ n -ℚ p
    inver[+] : ∀ (m : ℚ) → (m -ℚ m) ≡ 0ℚ

--lunit[×] a
-- Constants

ℚ→ℝ-helper : ∀ (q : ℚ ) → (∀(ε : ℚ) → ∀(a b : ℕ) → ε >ℚ 0ℚ → a >ᴺ ((λ x → 0) ε) → b >ᴺ ((λ x → 0) ε) → abs ((λ x → q) a -ℚ (λ x → q) b) ≤ℚ ε )
ℚ→ℝ-helper q (mkℚ (+_ n) denominator-1 cop) a b (*<* x) a>e→n b>e→n rewrite inver[+] q = *≤* (ℤprop.<⇒≤ x)
ℚ→ℝ-helper q (mkℚ (-[1+_] n) denominator-1 cop) a b (*<* ()) a>e→n b>e→n


_→ℝ : ℚ → ℝ
q →ℝ = ⟪ (λ x → q) , (λ x → 0) , ℚ→ℝ-helper q ⟫

0ᵣ : ℝ
0ᵣ = 0ℚ →ℝ

1ᵣ : ℝ
1ᵣ = 1ℚ →ℝ


-- Addition and multiplication


½a<a : ∀ (a : ℚ) → a >ℚ 0ℚ → ½ *ℚ a <ℚ a
½a<a a a>0 with lmono[*/<] a ½ 1ℚ (*<* (+<+ (s≤s (s≤s z≤n)))) a>0
... | prf rewrite runit[×] a | commu[×] a ½ = prf


-- look at that type line. Whew.
-- This is a top-level function replicating the lambda that would be the third argument to the outpt of _+ʳ_. Because the types are dependant, we have to list them all out.

add-helper : (f₁ : ( ℕ → ℚ )) → (ε→n₁ : (ℚ → ℕ )) → (∀(ε₁ : ℚ) → ∀(a₁ b₁ : ℕ) → ε₁ >ℚ 0ℚ → a₁ >ᴺ (ε→n₁ ε₁) → b₁ >ᴺ (ε→n₁ ε₁) → abs (f₁ a₁ -ℚ f₁ b₁) ≤ℚ ε₁ ) →
             (f₂ : ( ℕ → ℚ )) → (ε→n₂ : (ℚ → ℕ )) → (∀(ε₂ : ℚ) → ∀(a₂ b₂ : ℕ) → ε₂ >ℚ 0ℚ → a₂ >ᴺ (ε→n₂ ε₂) → b₂ >ᴺ (ε→n₂ ε₂) → abs (f₂ a₂ -ℚ f₂ b₂) ≤ℚ ε₂ ) →
             ∀(εₓ : ℚ) → ∀(aₓ bₓ : ℕ) → εₓ >ℚ 0ℚ → aₓ >ᴺ ((λ ε → ε→n₁ ( ½ *ℚ ε) +ᴺ ε→n₂ ( ½ *ℚ ε)) εₓ) → bₓ >ᴺ ((λ ε → ε→n₁ ( ½ *ℚ ε) +ᴺ ε→n₂ ( ½ *ℚ ε)) εₓ) →
             abs ((λ x → f₁ x +ℚ f₂ x) aₓ -ℚ (λ x → f₁ x +ℚ f₂ x) bₓ) ≤ℚ εₓ
  -- (∀(ε : ℚ) → ∀(a b : ℕ)
  -- → ε >ℚ 0ℚ
  -- → a >ᴺ (ε→n ε)
  -- → b >ᴺ (ε→n ε)
  -- → abs (f a -ℚ f b) ≤ℚ ε ) → ℝ



add-helper fᵃ ε→nᵃ prfᵃ fᵇ ε→nᵇ prfᵇ εₓ aₓ bₓ εₓ>0 aₓ>ε bₓ>ε with lmono[*/<] ½ 0ℚ εₓ εₓ>0 (*<* (+<+ (s≤s z≤n)))
... | ½ε>0 with prfᵃ (½ *ℚ εₓ) aₓ bₓ ½ε>0 (relim[+/<ᴺ] (ε→nᵃ ( ½ *ℚ εₓ)) (ε→nᵇ ( ½ *ℚ εₓ)) aₓ aₓ>ε) (relim[+/<ᴺ] (ε→nᵃ ( ½ *ℚ εₓ)) (ε→nᵇ ( ½ *ℚ εₓ)) bₓ bₓ>ε)
              | prfᵇ (½ *ℚ εₓ) aₓ bₓ ½ε>0 (lelim[+/<ᴺ] (ε→nᵃ ( ½ *ℚ εₓ)) (ε→nᵇ ( ½ *ℚ εₓ)) aₓ aₓ>ε) (lelim[+/<ᴺ] (ε→nᵃ ( ½ *ℚ εₓ)) (ε→nᵇ ( ½ *ℚ εₓ)) bₓ bₓ>ε)
... | ineqᵃ | ineqᵇ with (sum[≤] ineqᵃ ineqᵇ) ⊚[≤] (abs-split[+/≤] (fᵃ aₓ -ℚ fᵃ bₓ) (fᵇ aₓ -ℚ fᵇ bₓ))
... | joined rewrite assoc[+] (fᵃ aₓ -ℚ fᵃ bₓ) (ℚmod.- fᵃ aₓ) (ℚmod.- fᵇ bₓ)
                   | assoc[+] (fᵃ aₓ) (ℚmod.- fᵃ bₓ) (fᵇ aₓ)
                   | commu[+] (fᵇ aₓ) (ℚmod.- fᵃ bₓ)
                   | assoc[+] (fᵃ aₓ) (fᵇ aₓ) (ℚmod.- fᵃ bₓ)
                   | distr[-] ((fᵃ aₓ) +ℚ (fᵇ aₓ)) (fᵃ bₓ) (fᵇ bₓ)
                   = {!joined  !}

--prfᵃ (½ *ℚ εₓ) aₓ bₓ () (linear[<ᴺ/+] (ε→nᵃ ( ½ *ℚ εₓ)) (ε→nᵇ ( ½ *ℚ εₓ)) aₓ>ε) (linear[<ᴺ/+] (ε→nᵃ ( ½ *ℚ εₓ)) (ε→nᵇ ( ½ *ℚ εₓ)) bₓ>ε)

--(abs-split[+/≤]) ⊚[≤] ?

--Proof has three components:
--  1. Show ∣fₓ aₓ -ℚ fₓ bₓ∣ ≤ ∣fᵃ aₓ -ℚ fᵃ bₓ∣ + ∣fᵇ aₓ -ℚ fᵇ bₓ∣
--  2. Show ∣fᵃ aₓ -ℚ fᵃ bₓ∣ ≤ ½ *ℚ εₓ and ∣fᵇ aₓ -ℚ fᵇ bₓ∣ ≤ ½ *ℚ εₓ
--  3. Combine the two with a proof that (½ *ℚ εₓ) +ℚ (½ *ℚ εₓ) ≡ εₓ.


--  == To show ∣fᵃ aₓ -ℚ fᵃ bₓ∣ ≤ ½ *ℚ εₓ (and also fᵇ by an identical argument) ==
-- ((λ ε → ε→n₁ ( ½ *ℚ ε) +ᴺ ε→n₂ ( ½ *ℚ ε)) εₓ) εₓ <ᴺ aₓ
--≡ ε→n₁ ( ½ *ℚ ε) +ᴺ ε→n₂ ( ½ *ℚ ε)) εₓ

-- relim[<ᴺ/+] (ε→n₁ ( ½ *ℚ εₓ)) (ε→n₂ ( ½ *ℚ εₓ)) aₓ>ε
    --                                                [aₓ >ᴺ ((λ ε → ε→n₁ ( ½ *ℚ ε) +ᴺ ε→n₂ ( ½ *ℚ ε)) εₓ)]
    -- ε→n₁ ( ½ *ℚ εₓ) < (ε→n₁ ( ½ *ℚ εₓ) +ᴺ ε→n₂ ( ½ *ℚ εₓ)) < aₓ
-- aₓ>ε′ ≡ ε→n₁ ( ½ *ℚ εₓ) < aₓ
-- linear[<ᴺ/+] (ε→n₁ ( ½ *ℚ εₓ)) (ε→n₂ ( ½ *ℚ εₓ)) bₓ>ε
    --                                                [bₓ >ᴺ ((λ ε → ε→n₁ ( ½ *ℚ ε) +ᴺ ε→n₂ ( ½ *ℚ ε)) εₓ)]
    -- ε→n₁ ( ½ *ℚ εₓ) < (ε→n₁ ( ½ *ℚ εₓ) +ᴺ ε→n₂ ( ½ *ℚ εₓ)) < bₓ
-- bₓ>ε′ ≡ ε→n₁ ( ½ *ℚ εₓ) < bₓ

-- prfᵃ (½ *ℚ εₓ) aₓ bₓ aₓ>ε′ bₓ>ε′

-- prfᵃ (½ *ℚ εₓ) aₓ bₓ ½ε>0 (linear[+/<ᴺ] (ε→nᵃ ( ½ *ℚ εₓ)) (ε→nᵇ ( ½ *ℚ εₓ)) aₓ aₓ>ε) (linear[+/<ᴺ] (ε→nᵃ ( ½ *ℚ εₓ)) (ε→nᵇ ( ½ *ℚ εₓ)) bₓ bₓ>ε)


-- == To show ∣fₓ aₓ -ℚ fₓ bₓ∣ ≤ ∣fᵃ aₓ -ℚ fᵃ bₓ∣ + ∣fᵇ aₓ -ℚ fᵇ bₓ∣ ==
-- ((fᵃ aₓ +ℚ fᵇ aₓ) -ℚ (fᵃ bₓ +ℚ fᵇ bₓ))

-- ⟶ distr[-] ((fᵃ aₓ) +ℚ (fᵇ aₓ)) (fᵃ bₓ) (fᵇ bₓ)
-- (((fᵃ aₓ +ℚ fᵇ aₓ) +ℚ -fᵃ bₓ) +ℚ -fᵇ bₓ)

-- ⟶ assoc[+] (fᵃ aₓ) (fᵇ aₓ) (-fᵃ bₓ)
-- ((fᵃ aₓ +ℚ (fᵇ aₓ +ℚ -fᵃ bₓ)) +ℚ -fᵇ bₓ)

-- ⟶ commu[+] (fᵇ aₓ) (-fᵃ bₓ)
-- ((fᵃ aₓ +ℚ (-fᵃ bₓ +ℚ fᵇ aₓ)) +ℚ -fᵇ bₓ)

-- ⟶ assoc[+] (fᵃ aₓ) (-fᵃ bₓ) (fᵇ aₓ)
-- (((fᵃ aₓ +ℚ -fᵃ bₓ) +ℚ fᵇ aₓ) +ℚ -fᵇ bₓ)

-- ⟶ assoc[+] (fᵃ aₓ -ℚ fᵃ bₓ) (-fᵃ aₓ) (-fᵇ bₓ)
-- ((fᵃ aₓ +ℚ -fᵃ bₓ) +ℚ (fᵇ aₓ +ℚ -fᵇ bₓ))

-- == Combine ==

-- (sum[<] (∣fᵃ aₓ -ℚ fᵃ bₓ∣ ≤ ½ *ℚ εₓ) (∣fᵇ aₓ -ℚ fᵇ bₓ∣ ≤ ½ *ℚ εₓ)) ⊚[≤] (split[½/+] εₑ)

_+ʳ_ : ℝ → ℝ → ℝ
⟪ fᵃ , ε→nᵃ , prfᵃ ⟫ +ʳ ⟪ fᵇ , ε→nᵇ , prfᵇ ⟫ = ⟪ (λ x → fᵃ x +ℚ fᵇ x) -- Pointwise addition
                                               , (λ ε → ε→nᵃ ( ½ *ℚ ε) +ᴺ ε→nᵇ ( ½ *ℚ ε)) -- Sum the Ns for εs ½ the size
                                               , add-helper fᵃ ε→nᵃ prfᵃ fᵇ ε→nᵇ prfᵇ ⟫ -- We have
                                                -- ⟪  -- Pointwise addition
                                                -- ,  -- Take the sum of the N's for εs half the size
                                                -- ⟫ --

-ᵣ-helper : (f₁ : ( ℕ → ℚ )) → (ε→n₁ : (ℚ → ℕ )) → (∀(ε₁ : ℚ) → ∀(a₁ b₁ : ℕ) → ε₁ >ℚ 0ℚ → a₁ >ᴺ (ε→n₁ ε₁) → b₁ >ᴺ (ε→n₁ ε₁) → abs (f₁ a₁ -ℚ f₁ b₁) ≤ℚ ε₁ ) →
            (∀(ε : ℚ) → ∀(a b : ℕ) → ε >ℚ 0ℚ → a >ᴺ (ε→n₁ ε) → b >ᴺ (ε→n₁ ε) → abs ((λ x → ℚmod.- f₁ x) a -ℚ (λ x → ℚmod.- f₁ x) b) ≤ℚ ε )

-ᵣ-helper f ε→n prf ε a b ε>0 a>ε b>ε with ℚmod.- f a -ℚ ℚmod.- f b |  prf ε a b ε>0 a>ε b>ε
-ᵣ-helper f ε→n prf ε a b ε>0 a>ε b>ε | mkℚ (+_ n) denominator-1 cop | *≤* x = *≤* {! ↯  !}
-ᵣ-helper f ε→n prf ε a b ε>0 a>ε b>ε | mkℚ (-[1+_] n) denominator-1 cop | prf′ = {! prf′ !}

-ᵣ_ : ℝ → ℝ
-ᵣ ⟪ f , ε→n , prf ⟫ = ⟪ (λ x → ℚmod.- f x) , ε→n , -ᵣ-helper f ε→n prf ⟫

-- Addition Properies Lemmas
commu-helper : ∀ (f₁ f₂ : (ℕ → ℚ)) → ∀ (a : ℕ) → abs (f₁ a +ℚ f₂ a -ℚ (f₂ a +ℚ f₁ a)) ≡ 0ℚ
commu-helper f g a with f a | g a | ℚmod.- g a | ℚmod.- f a
... | fa | ga | nga | nfa rewrite distr[-] (fa +ℚ ga) (ga) (fa)
                                | assoc[+] (fa) (ga) (nga +ℚ nfa)
                                | assoc[+] (ga) (nga) (nfa)
                                | inver[+] (ga)
                                | lunit[+] nfa
                                = {!   !}

commu-helper′ : ∀ (f₁ f₂ : (ℕ → ℚ)) → ∀ (a : ℕ) → ∀ (ε : ℚ) → abs (f₁ a +ℚ f₂ a -ℚ (f₂ a +ℚ f₁ a)) ≤ℚ ε
commu-helper′ f g a ε rewrite commu-helper f g a | ℤprop.*-zeroˡ (↧ ε) = {!   !}



-- Addition Properties

commu[+ʳ] : ∀ (a b : ℝ ) → a +ʳ b ≃ʳ b +ʳ a
commu[+ʳ] ⟪ f₁ , ε→n₁ , prf₁ ⟫ ⟪ f₂ , ε→n₂ , prf₂ ⟫ = *≡* (λ x → 0) λ where ε a ε>0 a>0 → {!   !}

assoc[+ʳ] : ∀ (a b c : ℝ ) → a +ʳ (b +ʳ c) ≃ʳ (a +ʳ b) +ʳ c
assoc[+ʳ] a b c = *≡* (λ x → 0) (λ ε n ε>0 n>0 → {!   !})

lzero[+ʳ] : ∀ (a : ℝ) → (0ᵣ +ʳ a ≃ʳ a)
lzero[+ʳ] a = {!   !}

inver[+ʳ] : ∀ (a : ℝ) → (a +ʳ (-ᵣ a) ≃ʳ 0ᵣ)
inver[+ʳ] a = {!   !}

--Multiplication

--TO DO: Update ε→nˣ
mul-helper : (f₁ : ( ℕ → ℚ )) → (ε→n₁ : (ℚ → ℕ )) → (∀(ε₁ : ℚ) → ∀(a₁ b₁ : ℕ) → ε₁ >ℚ 0ℚ → a₁ >ᴺ (ε→n₁ ε₁) → b₁ >ᴺ (ε→n₁ ε₁) → abs (f₁ a₁ -ℚ f₁ b₁) ≤ℚ ε₁) →
             (f₂ : ( ℕ → ℚ )) → (ε→n₂ : (ℚ → ℕ )) → (∀(ε₂ : ℚ) → ∀(a₂ b₂ : ℕ) → ε₂ >ℚ 0ℚ → a₂ >ᴺ (ε→n₂ ε₂) → b₂ >ᴺ (ε→n₂ ε₂) → abs (f₂ a₂ -ℚ f₂ b₂) ≤ℚ ε₂) →
             ∀(εₓ : ℚ) → ∀(aₓ bₓ : ℕ) → εₓ >ℚ 0ℚ → aₓ >ᴺ ((λ ε → ε→n₁ ( ½ *ℚ ε) +ᴺ ε→n₂ ( ½ *ℚ ε)) εₓ) → bₓ >ᴺ ((λ ε → ε→n₁ ( ½ *ℚ ε) +ᴺ ε→n₂ ( ½ *ℚ ε)) εₓ) →
             abs ((λ x → f₁ x *ℚ f₂ x) aₓ -ℚ (λ x → f₁ x *ℚ f₂ x) bₓ) ≤ℚ εₓ

mul-helper fᵃ ε→nᵃ prfᵃ fᵇ ε→nᵇ prfᵇ εₓ aₓ bₓ εₓ>0 aₓ>ε bₓ>ε = {!   !}

_×ʳ_ : ℝ → ℝ → ℝ
⟪ fᵃ , ε→nᵃ , prfᵃ ⟫ ×ʳ ⟪ fᵇ , ε→nᵇ , prfᵇ ⟫  with (λ x → fᵃ x *ℚ fᵇ x) | (λ ε → ε→nᵃ ( ½ *ℚ ε) *ᴺ ε→nᵇ ( ½ *ℚ ε))
... | fˣ | ε→nˣ = ⟪ fˣ , ε→nˣ , (λ where ε a b ε>0 a>nˣ b>nˣ → {!   !}) ⟫
