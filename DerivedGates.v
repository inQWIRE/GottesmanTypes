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

(* Types on Y *)

Lemma HTypesY : H' 0 :: Y → - Y.
Proof. type_check_base. Qed.

Lemma STypesY : S' 0 :: Y → - X.
Proof. type_check_base. Qed.

Lemma ITypesY : I' 0 :: Y → Y.
Proof. type_check_base. Qed.

Lemma XTypesY : X' 0 :: Y → - Y.
Proof. type_check_base. Qed.

Lemma ZTypesY : Z' 0 :: Y → - Y.
Proof. type_check_base. Qed.

Lemma YTypesY : Y' 0 :: Y → Y.
Proof. type_check_base. Qed.

Lemma CNOTTypesY : CNOT 0 1 :: (Y ⊗ I → Y ⊗ X) ∩ (I ⊗ Y → Z ⊗ Y).
Proof. type_check_base. Qed.

Lemma CZTypesY : CZ 0 1 :: (Y ⊗ I → Y ⊗ Z) ∩ (I ⊗ Y → Z ⊗ Y).
Proof. type_check_base. Qed.

(* All types for CNOT and CZ *)

Lemma CNOTTypesPairs : CNOT 0 1 :: (X ⊗ X →  X ⊗ I) ∩
                                  (X ⊗ Y →  Y ⊗ Z) ∩
                                  (X ⊗ Z → -Y ⊗ Y) ∩
                                  (Y ⊗ X →  Y ⊗ I) ∩
                                  (Y ⊗ Y → -X ⊗ Z) ∩
                                  (Y ⊗ Z →  X ⊗ Y) ∩
                                  (Z ⊗ X →  Z ⊗ X) ∩
                                  (Z ⊗ Y →  I ⊗ Y) ∩
                                  (Z ⊗ Z →  I ⊗ Z).
Proof. type_check_base. Qed.

Lemma CZTypesPairs : CZ 0 1 :: (X ⊗ X →  Y ⊗ Y) ∩
                              (X ⊗ Y → -Y ⊗ X) ∩
                              (X ⊗ Z →  X ⊗ I) ∩
                              (Y ⊗ X → -X ⊗ Y) ∩
                              (Y ⊗ Y →  X ⊗ X) ∩
                              (Y ⊗ Z →  Y ⊗ I) ∩
                              (Z ⊗ X →  I ⊗ X) ∩
                              (Z ⊗ Y →  I ⊗ Y) ∩
                              (Z ⊗ Z →  Z ⊗ Z).
Proof. type_check_base. Qed.

  



