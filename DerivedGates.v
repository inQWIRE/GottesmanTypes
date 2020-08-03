Require Export Programs.

(* I, X, Y and Z as derived gates *)
Definition Z' n : prog := S' n ; S' n.
Definition X' n : prog := H' n ; Z' n; H' n.
Definition Y' n : prog := S' n; X' n; Z' n; S' n.
Definition I' n : prog := H' n; H' n.

(* Other common gates *)
Definition CZ m n : prog := H' n ; CNOT m n ; H' n.
Definition SWAP m n : prog := CNOT m n; CNOT n m; CNOT m n.

Lemma ITypes : I' 0 :: (X → X) ∩ (Z → Z).
Proof. type_check_base. Qed.

Lemma ZTypes : Z' 0 :: (X → -X) ∩ (Z → Z).
Proof. type_check_base. Qed.

Lemma XTypes : X' 0 :: (X → X) ∩ (Z → -Z).
Proof. type_check_base. Qed.

Lemma YTypes : Y' 0 :: (X → -X) ∩ (Z → -Z).
Proof. type_check_base. Qed.

Lemma CZTypes : CZ 0 1 :: (X ⊗ I → X ⊗ Z) ∩ (I ⊗ X → Z ⊗ X) ∩
                         (Z ⊗ I → Z ⊗ I) ∩ (I ⊗ Z → I ⊗ Z).
Proof. type_check_base. Qed.

Lemma SWAPTypes : (SWAP 0 1) :: (X ⊗ I → I ⊗ X) ∩ (I ⊗ X → X ⊗ I) ∩
                             (Z ⊗ I → I ⊗ Z) ∩ (I ⊗ Z → Z ⊗ I).
Proof. type_check_base. Qed.

