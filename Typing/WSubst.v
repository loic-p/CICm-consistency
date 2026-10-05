(** The substitution equations of the W step.

    These are what `Typing/Subst.v` needs for the four W rules, and they are
    the reason this development moved from Autosubst2 to Sulfur: under
    `asimpl` the last one did not terminate, in any of five formulations.
    Under `rasimpl` the whole file is a few seconds.

    The one discipline required: SHIFTS MUST BE WRITTEN IN THE ALGEBRA
    (`rcomp ↑ ↑`, `.:s`), never as a raw lambda `fun i => var_tm (S (S i))`,
    which rasimpl cannot push a composition through. *)

From CICM Require Import Syntax.Ann Typing.Rules.

(* ---- renaming ---- *)

Lemma wbr_ren k A B r :
  (wbr k A B) ⟨up_ren r⟩ = wbr k (A ⟨r⟩) (B ⟨up_ren r⟩).
Proof. unfold wbr; rasimpl; reflexivity. Qed.

Lemma wih_ren n k A B C r :
  (wih n k A B C) ⟨up_ren (up_ren r)⟩
  = wih n k (A ⟨r⟩) (B ⟨up_ren r⟩) (C ⟨up_ren r⟩).
Proof. unfold wih, sh3; rasimpl; reflexivity. Qed.

Lemma wsup_ty_ren k A B C r :
  (wsup_ty k A B C) ⟨up_ren (up_ren (up_ren r))⟩
  = wsup_ty k (A ⟨r⟩) (B ⟨up_ren r⟩) (C ⟨up_ren r⟩).
Proof. unfold wsup_ty, sh3; rasimpl; reflexivity. Qed.

Lemma wih_val_ren n k A B C s a f r :
  (wih_val n k A B C s a f) ⟨r⟩
  = wih_val n k (A ⟨r⟩) (B ⟨up_ren r⟩) (C ⟨up_ren r⟩)
      (s ⟨up_ren (up_ren (up_ren r))⟩) (a ⟨r⟩) (f ⟨r⟩).
Proof. unfold wih_val, wsub; rasimpl; reflexivity. Qed.

(* ---- substitution ---- *)

Lemma wbr_subst k A B s :
  (wbr k A B) [up_subst s] = wbr k (A [s]) (B [up_subst s]).
Proof. unfold wbr; rasimpl; reflexivity. Qed.

Lemma wih_subst n k A B C s :
  (wih n k A B C) [up_subst (up_subst s)]
  = wih n k (A [s]) (B [up_subst s]) (C [up_subst s]).
Proof. unfold wih, sh3; rasimpl; reflexivity. Qed.

Lemma wsup_ty_subst k A B C s :
  (wsup_ty k A B C) [up_subst (up_subst (up_subst s))]
  = wsup_ty k (A [s]) (B [up_subst s]) (C [up_subst s]).
Proof. unfold wsup_ty, sh3; rasimpl; reflexivity. Qed.

Lemma wih_val_subst n k A B C st a f s :
  (wih_val n k A B C st a f) [s]
  = wih_val n k (A [s]) (B [up_subst s]) (C [up_subst s])
      (st [up_subst (up_subst (up_subst s))]) (a [s]) (f [s]).
Proof. unfold wih_val, wsub; rasimpl; reflexivity. Qed.

(* ---- what the c_wrec_sup case needs: the contractum commutes ---- *)

Lemma wrec_sup_contractum_ren n k A B C st a f r :
  (st [ wih_val n k A B C st a f .: (f .: a ..) ]) ⟨r⟩
  = (st ⟨up_ren (up_ren (up_ren r))⟩)
      [ wih_val n k (A ⟨r⟩) (B ⟨up_ren r⟩) (C ⟨up_ren r⟩)
          (st ⟨up_ren (up_ren (up_ren r))⟩) (a ⟨r⟩) (f ⟨r⟩)
        .: ((f ⟨r⟩) .: (a ⟨r⟩) ..) ].
Proof. rewrite <- wih_val_ren; rasimpl; reflexivity. Qed.

Lemma wrec_sup_contractum_subst n k A B C st a f s :
  (st [ wih_val n k A B C st a f .: (f .: a ..) ]) [s]
  = (st [up_subst (up_subst (up_subst s))])
      [ wih_val n k (A [s]) (B [up_subst s]) (C [up_subst s])
          (st [up_subst (up_subst (up_subst s))]) (a [s]) (f [s])
        .: ((f [s]) .: (a [s]) ..) ].
Proof. rewrite <- wih_val_subst; rasimpl; reflexivity. Qed.

(* ---- the type of a tree's branching function, under a renaming and under
       a substitution: what the t_sup and c_sup cases of Typing/Subst.v need ---- *)

Lemma sup_fun_ren k A B a r :
  (pi k (B [a..]) ((wt k A B) ⟨↑⟩)) ⟨r⟩
  = pi k ((B ⟨up_ren r⟩) [(a ⟨r⟩)..]) ((wt k (A ⟨r⟩) (B ⟨up_ren r⟩)) ⟨↑⟩).
Proof. rasimpl; reflexivity. Qed.

Lemma sup_fun_subst k A B a s :
  (pi k (B [a..]) ((wt k A B) ⟨↑⟩)) [s]
  = pi k ((B [up_subst s]) [(a [s])..]) ((wt k (A [s]) (B [up_subst s])) ⟨↑⟩).
Proof. rasimpl; reflexivity. Qed.
