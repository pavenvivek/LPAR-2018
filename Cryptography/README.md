# CryptDB in Homotopy Type Theory
This repository contains implementation for CryptDB.

We have used an automation tool to generate the code for higher inductive type. The tool is still in development.

To understand what the tool generates, see the following example:

module Circle1 where
  private 
    data S₁* : Set where
      base* : S₁*

  S : Set
  S = S*

  base : S
  base = base*

  postulate 
    loop : base ≡ base

  recS : S → (C : Set) → (cbase : C) → (cloop : cbase ≡ cbase) → C
  recS base* C cbase cloop = cbase

  postulate
    βrecS : (C : Set) → (cbase : C) → (cloop : cbase ≡ cbase) → 
      ap (λ x → recS x C cbase cloop) loop ≡ cloop

  indS : (circle : S) → (C : S → Set) → 
    (cbase : C base) → (cloop : transport C loop cbase ≡ cbase) → C circle
  indS base* C cbase cloop = cbase

  postulate
    βindS : (C : S → Set) → 
      (cbase : C base) → (cloop : transport C loop cbase ≡ cbase) → 
      apd (λ x → indS x C cbase cloop) loop ≡ cloop

The tool automates the generation of code in the above module. Please see the test cases in Automation/test folder for more information.
