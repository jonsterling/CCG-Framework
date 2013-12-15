module test where

open import ccg

data base : Set where
  N NP : base
  
data lex_ : syn _ → Set where
  dog : lex ⟨ N ⟩
  the : lex ⟨ NP ⟩ /[ ◆ ] ⟨ N ⟩

infixl 9 lex_
open Terms lex_

the-dog : trm ⟨ NP ⟩
the-dog = [ the ] > [ dog ]


