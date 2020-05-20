(* Example 11: Remove XOR *)

(** * Own examples *)

(** * Proofs about derived unitaries *)

Lemma X_X1 : @h_eval 1 (X 0) [XX] = [XX].
Proof. reflexivity. Qed.
Lemma X_Z1 : @h_eval 1 (X 0) [ZZ] = [-1 * ZZ].
Proof. reflexivity. Qed.
Lemma Y_X1 : @h_eval 1 (Y 0) [XX] = [-1 * XX].
Proof. reflexivity. Qed.
Lemma Y_Z1 : @h_eval 1 (Y 0) [ZZ] = [-1 * ZZ].
Proof. reflexivity. Qed.
Lemma Z_X1 : @h_eval 1 (Z 0) [XX] = [-1 * XX].
Proof. reflexivity. Qed.
Lemma Z_Z1 : @h_eval 1 (Z 0) [ZZ] = [ZZ].
Proof. reflexivity. Qed.

Lemma CZ_X1 : @h_eval 2 (CZ 0 1) [XX,II] = [XX,ZZ].
Proof. reflexivity. Qed.
Lemma CZ_Z1 : @h_eval 2 (CZ 0 1) [ZZ,II] = [ZZ,II].
Proof. reflexivity. Qed.
Lemma CZ_X2 : @h_eval 2 (CZ 0 1) [II,XX] = [ZZ,XX].
Proof. reflexivity. Qed.
Lemma CZ_Z2 : @h_eval 2 (CZ 0 1) [II,ZZ] = [II,ZZ].
Proof. reflexivity. Qed.

(* Superdense coding *)

Definition bell00 : prog 4 :=
  H 2;
  CNOT 2 3.

Definition encode : prog 4 :=
    CZ 0 2; CNOT 1 2.

Definition decode : prog 4 :=
  CNOT 2 3;
  H 2.

Definition superdense := bell00 ; encode; decode.

Compute (h_eval superdense [ZZ,ZZ,ZZ,ZZ]). (* I, I, Z, Z *)
Compute (h_eval superdense [II,ZZ,ZZ,ZZ]). (* Z, I, Z, Z *)
Compute (h_eval superdense [ZZ,II,ZZ,ZZ]). (* I, Z, Z, Z *)
Compute (h_eval superdense [II,II,ZZ,ZZ]). (* Z, Z, Z, Z *)
Compute (h_eval superdense [ZZ,ZZ,ZZ,II]). (* I, Z, Z, I *)
Compute (h_eval superdense [ZZ,ZZ,II,ZZ]). (* Z, I, I, Z *)

Compute (h_eval superdense [ZZ,II,II,II]). (* Z, I, I, I *)
Compute (h_eval superdense [II,ZZ,II,II]). (* I, Z, I, I *)
Compute (h_eval superdense [II,II,ZZ,II]). (* Z, I, Z, I *)
Compute (h_eval superdense [II,II,II,ZZ]). (* I, Z, I, Z *)


Lemma superdense_ZZ : h_eval superdense [ZZ,ZZ,ZZ,ZZ] = [II,II,ZZ,ZZ].
Proof. reflexivity. Qed.

(* GHZ state *)

Compute (h_eval (CNOT 0 1) [XX*ZZ, ZZ]). (* X, XZ *)

Definition GHZ3 : prog :=
  H 0;
  CNOT 0 1;
  CNOT 1 2.

Compute (h_eval GHZ3 [ZZ,ZZ,ZZ]). (* XZ, X, XZ *)

Compute (h_eval GHZ3 [XX,II,II]). (* Z, I, I *)
Compute (h_eval GHZ3 [II,XX,II]). (* I, X, X *)
Compute (h_eval GHZ3 [II,II,XX]). (* I, I, X *)
Compute (h_eval GHZ3 [II,ZZ,ZZ]). (* Z, I, Z *)
Compute (h_eval GHZ3 [XX,ZZ,ZZ]). (* I, I, Z *)
Compute (h_eval GHZ3 [XX,II,ZZ]). (* Z, Z, Z *)
Compute (h_eval GHZ3 [XX,ZZ,II]). (* I, Z, I *)

Compute (h_eval GHZ3 [ZZ,II,II]). (* X, X, X *)
Compute (h_eval GHZ3 [II,ZZ,II]). (* Z, Z, I *)
Compute (h_eval GHZ3 [II,II,ZZ]). (* I, Z, Z *)


Compute (h_eval (CNOT 1 2; CNOT 0 1) [XX*ZZ,XX,XX*ZZ]). (* X, Z, Z ??? *)
Compute (h_eval (CNOT 0 1; CNOT 1 2) [XX*ZZ,XX,XX*ZZ]). (* X, Z, Z ??? *)

(** Honda motivating example *)

Definition SEP0 := GHZ3 ; CNOT 0 1; CNOT 0 2.

Compute (h_eval SEP0 [ZZ,II,II]). (* X, I, I *)
Compute (h_eval SEP0 [II,ZZ,II]). (* I, Z, I *)
Compute (h_eval SEP0 [II,II,ZZ]). (* I, Z, Z *) (* becomes I, I, Z *)

(* Result : X × Z × Z *)

(** Unentangling one qubit *)

Compute (h_eval (GHZ3;CNOT 1 2) [ZZ,II,II]). (* X, X, I *)
Compute (h_eval (GHZ3;CNOT 1 2) [II,ZZ,II]). (* Z, Z, I *)
Compute (h_eval (GHZ3;CNOT 1 2) [II,II,ZZ]). (* I, I, Z *)

Compute (h_eval (GHZ3;CNOT 2 1) [ZZ,II,II]). (* X, I, X *)
Compute (h_eval (GHZ3;CNOT 2 1) [II,ZZ,II]). (* Z, Z, Z *) (* becomes Z, I, Z *)
Compute (h_eval (GHZ3;CNOT 2 1) [II,II,ZZ]). (* I, Z, I *)
