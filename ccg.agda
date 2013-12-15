module ccg where

record ⊤ : Set where constructor tt
data ⊥ : Set where

data mod : Set where
  ∙ ◆ × ★ : mod

data Dec (P : Set) : Set where
  yes : P → Dec P
  no : (P → ⊥) → Dec P

_≤_ : mod → mod → Set
∙ ≤ n = ⊤
◆ ≤ ◆ = ⊤
◆ ≤ ★ = ⊤
× ≤ × = ⊤
× ≤ ★ = ⊤
★ ≤ ★ = ⊤
_ ≤ _ = ⊥

_≤?_ : (m n : mod) → Dec (m ≤ n)
∙ ≤? n = yes tt
◆ ≤? ∙ = no (λ z → z)
◆ ≤? ◆ = yes tt
◆ ≤? × = no (λ z → z)
◆ ≤? ★ = yes tt
× ≤? ∙ = no (λ z → z)
× ≤? ◆ = no (λ z → z)
× ≤? × = yes tt
× ≤? ★ = yes tt
★ ≤? ∙ = no (λ z → z)
★ ≤? ◆ = no (λ z → z)
★ ≤? × = no (λ z → z)
★ ≤? ★ = yes tt

_∨_ : (m n : mod) → mod
m ∨ n with m ≤? n
... | yes p = m
... | no np = n

  
data syn (b : Set) : Set where
  ⟨_⟩ : b → syn _
  _/[_]_ : (t : syn b) (m : mod) (s : syn b) → syn _
  _\[_]_ : (t : syn b) (m : mod) (s : syn b) → syn _

module Terms {b : Set} (lex : syn b → Set) where
  data trm_ : syn b → Set where

    -- embedding of lexical items
    [_] : ∀ {s} → lex s → trm s

    -- forward application
    _>_ : ∀ {s t m} → trm t /[ m ] s → trm s → trm t

    -- backward application
    _<_ : ∀ {s t m} → trm s → trm t \[ m ] s → trm t 
  
    -- forward harmonic composition
    _>B_ : ∀ {x y z m n} {_ : ◆ ≤ m} {_ : ◆ ≤ n} → trm x /[ m ] y → trm y /[ n ] z → trm x /[ m ∨ n ] z
  
    -- backward harmonic composition
    _<B_ : ∀ {x y z m n} {_ : ◆ ≤ m} {_ : ◆ ≤ n} → trm y \[ m ] z → trm x \[ n ] y → trm x \[ n ∨ m ] z
  
    -- forward crossed composition
    _>B×_ : ∀ {x y z m n} {_ : × ≤ m} {_ : × ≤ n} → trm x /[ m ] y → trm y \[ n ] z →  trm x \[ m ∨ n ] z
  
    -- backward crossed composition
    _<B×_ : ∀ {x y z m n} {_ : × ≤ m} {_ : × ≤ n} → trm y /[ m ] z → trm x \[ n ] y →  trm x /[ n ∨ m ] z

    -- forward type raising
    _>T_ : ∀ {x} → trm x → ∀ {y} → trm y /[ ★ ] (y \[ ★ ] x)

    -- backward type raising
    _<T_ : ∀ {x} → trm x → ∀ {y} → trm y \[ ★ ] (y /[ ★ ] x)
    
  infixl 9 trm_
