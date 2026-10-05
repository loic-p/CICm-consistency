From CICM Require Import Syntax.Ann.
From CICM Require Import Typing.Rules Typing.WSubst.
From Stdlib Require Import Arith Lia.

Open Scope list_scope.

(* ------------------------------------------------------------------ *)
(* Renaming and substitution are admissible.                           *)
(*                                                                    *)
(* This is what the layer-2 fundamental lemma needs and nothing else in *)
(* the development did: a rule whose CONCLUSION type is a substitution   *)
(* instance (t_app, t_pair, t_snd, t_natrec, and their conversion         *)
(* counterparts) has to know that that type is itself well typed, because  *)
(* functionality of the interpretation is proved by induction on typing.   *)
(*                                                                    *)
(* The statements are Prop-valued -- `inhabited (ty …)` -- for two        *)
(* reasons: one Combined Scheme then covers the three mutual judgements,  *)
(* and nothing downstream needs the derivation itself, only its           *)
(* existence, since `funtm` consumes a derivation and yields a Prop.      *)
(* ------------------------------------------------------------------ *)

Scheme wfc_min := Minimality for wfc Sort Prop
  with ty_min := Minimality for ty Sort Prop
  with cv_min := Minimality for cv Sort Prop.
Combined Scheme wty_min from wfc_min, ty_min, cv_min.

(* ---- renaming ---- *)

Definition ren_ok (xi : nat -> nat) (G D : ctx) : Prop :=
  forall i A, lookup i G A -> lookup (xi i) D (A ⟨xi⟩).

Lemma ren_ok_shift G A : ren_ok ↑ G (A :: G).
Proof. intros i B H; apply lookup_S; exact H. Qed.

Lemma ren_ok_up xi G D A :
  ren_ok xi G D -> ren_ok (up_ren xi) (A :: G) (A ⟨xi⟩ :: D).
Proof.
  intros H i B HB; inversion HB; subst.
  - replace ((A ⟨↑⟩) ⟨up_ren xi⟩) with ((A ⟨xi⟩) ⟨↑⟩)
      by (rasimpl; reflexivity).
    apply lookup_O.
  - match goal with
    | H0 : lookup ?i0 G ?A0 |- _ =>
        replace ((A0 ⟨↑⟩) ⟨up_ren xi⟩) with ((A0 ⟨xi⟩) ⟨↑⟩)
          by (rasimpl; reflexivity);
        apply lookup_S; apply H; exact H0
    end.
Qed.

Lemma nrec_succ_ren (C : tm) xi :
  (nrec_succ C) ⟨up_ren (up_ren xi)⟩ = nrec_succ (C ⟨up_ren xi⟩).
Proof. unfold nrec_succ; rasimpl; reflexivity. Qed.

Lemma nrec_succ_subst (C : tm) sigma :
  (nrec_succ C) [up_subst (up_subst sigma)] = nrec_succ (C [up_subst sigma]).
Proof. unfold nrec_succ; rasimpl; reflexivity. Qed.

(* nrec_succ as a composite of the three operations the SEMANTIC substitution
   lemma provides -- weaken in the tail, replace the nat variable by its own
   successor, weaken at the front -- which is how the interpretation reads the
   step's type (Interp/Fund.v's ity_nrec_succ). *)
Lemma nrec_succ_as (C : tm) :
  nrec_succ C = ((C ⟨up_ren ↑⟩) [(succ (var_tm 0))..]) ⟨↑⟩.
Proof. unfold nrec_succ; rasimpl; reflexivity. Qed.

(* and the same shape for the two types `wrec` substitutes into: `wih`'s
   codomain and `wsup_ty` are both `C [ a .:s sh3 ]`, which is C weakened by
   three entries under its own binder, with `a` put for that binder. *)
Lemma wsub3_as (C a : tm) : C [ a .:s sh3 ] = (C ⟨up_ren sh3⟩) [ a .. ].
Proof. rasimpl; reflexivity. Qed.

(* and the three weakenings that put C's own binder over the step's three
   entries, composed *)
Lemma ren3_as (C : tm) : ((C ⟨up_ren ↑⟩) ⟨up_ren ↑⟩) ⟨up_ren ↑⟩ = C ⟨up_ren sh3⟩.
Proof. rasimpl; reflexivity. Qed.

Lemma sh3_as (t : tm) : ((t ⟨↑⟩) ⟨↑⟩) ⟨↑⟩ = t ⟨sh3⟩.
Proof. rasimpl; reflexivity. Qed.

(* the eta-expansion's codomain: shifting past the bound variable and then
   substituting it back is the identity.  `t_app` produces
   `(B ⟨up_ren ↑⟩) [(var_tm 0)..]` where the rule wants `B`. *)
Lemma eta_cod_sub (B : tm) : (B ⟨up_ren ↑⟩) [(var_tm 0)..] = B.
Proof. rasimpl; reflexivity. Qed.

Lemma eta_ren (k : nat) (A B f : tm) xi :
  (lam k A B (app (A ⟨↑⟩) (B ⟨up_ren ↑⟩) (f ⟨↑⟩) (var_tm 0))) ⟨xi⟩
  = lam k (A ⟨xi⟩) (B ⟨up_ren xi⟩)
      (app ((A ⟨xi⟩) ⟨↑⟩) ((B ⟨up_ren xi⟩) ⟨up_ren ↑⟩)
           ((f ⟨xi⟩) ⟨↑⟩) (var_tm 0)).
Proof. rasimpl; reflexivity. Qed.

Lemma eta_subst (k : nat) (A B f : tm) sigma :
  (lam k A B (app (A ⟨↑⟩) (B ⟨up_ren ↑⟩) (f ⟨↑⟩) (var_tm 0))) [sigma]
  = lam k (A [sigma]) (B [up_subst sigma])
      (app ((A [sigma]) ⟨↑⟩) ((B [up_subst sigma]) ⟨up_ren ↑⟩)
           ((f [sigma]) ⟨↑⟩) (var_tm 0)).
Proof. rasimpl; reflexivity. Qed.

Lemma rec_succ_ren (C z s n : tm) xi :
  (s [ (natrec C z s n) .: n .. ]) ⟨xi⟩
  = (s ⟨up_ren (up_ren xi)⟩)
      [ (natrec (C ⟨up_ren xi⟩) (z ⟨xi⟩)
           (s ⟨up_ren (up_ren xi)⟩) (n ⟨xi⟩)) .: (n ⟨xi⟩) .. ].
Proof. rasimpl; reflexivity. Qed.

Lemma rec_succ_subst (C z s n : tm) sigma :
  (s [ (natrec C z s n) .: n .. ]) [sigma]
  = (s [up_subst (up_subst sigma)])
      [ (natrec (C [up_subst sigma]) (z [sigma])
           (s [up_subst (up_subst sigma)]) (n [sigma])) .: (n [sigma]) .. ].
Proof. rasimpl; reflexivity. Qed.

(* The step of a W recursion lives in a three-entry context whose types the
   rule now carries (see Typing/Rules.v).  Renaming that context is the only
   place where the W cases below differ from the Pi and Sigma ones. *)
Lemma ren_ok_wstep xi G D k n A B C (Hxi : ren_ok xi G D) :
  ren_ok (up_ren (up_ren (up_ren xi)))
    (wih n k A B C :: wbr k A B :: A :: G)
    (wih n k (A ⟨xi⟩) (B ⟨up_ren xi⟩) (C ⟨up_ren xi⟩)
       :: wbr k (A ⟨xi⟩) (B ⟨up_ren xi⟩) :: A ⟨xi⟩ :: D).
Proof.
  pose proof (ren_ok_up xi G D A Hxi) as H1.
  pose proof (ren_ok_up (up_ren xi) (A :: G) (A ⟨xi⟩ :: D) (wbr k A B) H1) as H2.
  rewrite wbr_ren in H2.
  pose proof (ren_ok_up (up_ren (up_ren xi)) (wbr k A B :: A :: G) _
                (wih n k A B C) H2) as H3.
  rewrite wih_ren in H3.
  exact H3.
Qed.

Theorem renaming :
  (forall G, wfc G -> True)
  /\ (forall G t A, ty G t A -> forall D xi, ren_ok xi G D -> inhabited (wfc D) ->
        inhabited (ty D (t ⟨xi⟩) (A ⟨xi⟩)))
  /\ (forall G t u A, cv G t u A -> forall D xi, ren_ok xi G D -> inhabited (wfc D) ->
        inhabited (cv D (t ⟨xi⟩) (u ⟨xi⟩) (A ⟨xi⟩))).
Proof.
  apply wty_min.
  - (* w_nil *) exact I.
  - (* w_cons *) intros; exact I.
  - (* t_var *) intros G i A W IHW Hl D xi Hxi [wD].
    exact (inhabits (t_var D (xi i) (A ⟨xi⟩) wD (Hxi i A Hl))).
  - (* t_conv *) intros G t A B k dt IHt dA IHA dB IHB c IHc D xi Hxi [wD].
    destruct (IHt D xi Hxi (inhabits wD)) as [dt'].
    destruct (IHA D xi Hxi (inhabits wD)) as [dA'].
    destruct (IHB D xi Hxi (inhabits wD)) as [dB'].
    destruct (IHc D xi Hxi (inhabits wD)) as [c'].
    exact (inhabits (t_conv D _ _ _ k dt' dA' dB' c')).
  - (* t_univ *) intros G k j Hjk W IHW D xi Hxi [wD].
    exact (inhabits (t_univ D k j Hjk wD)).
  - (* t_up *) intros G j A dA IHA D xi Hxi [wD].
    destruct (IHA D xi Hxi (inhabits wD)) as [dA'].
    exact (inhabits (t_up D j _ dA')).
  - (* t_up_tm *) intros G j A t dA IHA dt IHt D xi Hxi [wD].
    destruct (IHA D xi Hxi (inhabits wD)) as [dA'].
    destruct (IHt D xi Hxi (inhabits wD)) as [dt'].
    exact (inhabits (t_up_tm D j _ _ dA' dt')).
  - (* t_pi *) intros G k i j A B Hik Hjk dA IHA dB IHB D xi Hxi [wD].
    destruct (IHA D xi Hxi (inhabits wD)) as [dA'].
    destruct (IHB (A ⟨xi⟩ :: D) (up_ren xi) (ren_ok_up xi G D A Hxi)
                (inhabits (w_cons D _ _ wD dA'))) as [dB'].
    exact (inhabits (t_pi D k i j _ _ Hik Hjk dA' dB')).
  - (* t_lam *) intros G k i j A B t Hik Hjk dA IHA dB IHB dt IHt D xi Hxi [wD].
    destruct (IHA D xi Hxi (inhabits wD)) as [dA'].
    pose proof (inhabits (w_cons D (A ⟨xi⟩) _ wD dA')) as wD'.
    destruct (IHB (A ⟨xi⟩ :: D) (up_ren xi) (ren_ok_up xi G D A Hxi) wD') as [dB'].
    destruct (IHt (A ⟨xi⟩ :: D) (up_ren xi) (ren_ok_up xi G D A Hxi) wD') as [dt'].
    exact (inhabits (t_lam D k i j _ _ _ Hik Hjk dA' dB' dt')).
  - (* t_app *) intros G k i j A B f u Hik Hjk dA IHA dB IHB df IHf du IHu D xi Hxi [wD].
    destruct (IHA D xi Hxi (inhabits wD)) as [dA'].
    destruct (IHB (A ⟨xi⟩ :: D) (up_ren xi) (ren_ok_up xi G D A Hxi)
                (inhabits (w_cons D _ _ wD dA'))) as [dB'].
    destruct (IHf D xi Hxi (inhabits wD)) as [df'].
    destruct (IHu D xi Hxi (inhabits wD)) as [du'].
    replace ((B [u..]) ⟨xi⟩) with ((B ⟨up_ren xi⟩) [(u ⟨xi⟩)..])
      by (rasimpl; reflexivity).
    exact (inhabits (t_app D k i j _ _ _ _ Hik Hjk dA' dB' df' du')).
  - (* t_sig *) intros G k i j A B Hik Hjk dA IHA dB IHB D xi Hxi [wD].
    destruct (IHA D xi Hxi (inhabits wD)) as [dA'].
    destruct (IHB (A ⟨xi⟩ :: D) (up_ren xi) (ren_ok_up xi G D A Hxi)
                (inhabits (w_cons D _ _ wD dA'))) as [dB'].
    exact (inhabits (t_sig D k i j _ _ Hik Hjk dA' dB')).
  - (* t_pair *) intros G k i j A B t u Hik Hjk dA IHA dB IHB dt IHt du IHu D xi Hxi [wD].
    destruct (IHA D xi Hxi (inhabits wD)) as [dA'].
    destruct (IHB (A ⟨xi⟩ :: D) (up_ren xi) (ren_ok_up xi G D A Hxi)
                (inhabits (w_cons D _ _ wD dA'))) as [dB'].
    destruct (IHt D xi Hxi (inhabits wD)) as [dt'].
    destruct (IHu D xi Hxi (inhabits wD)) as [du'].
    replace ((B [t..]) ⟨xi⟩) with ((B ⟨up_ren xi⟩) [(t ⟨xi⟩)..]) in du'
      by (rasimpl; reflexivity).
    exact (inhabits (t_pair D k i j _ _ _ _ Hik Hjk dA' dB' dt' du')).
  - (* t_fst *) intros G k i j A B p Hik Hjk dA IHA dB IHB dp IHp D xi Hxi [wD].
    destruct (IHA D xi Hxi (inhabits wD)) as [dA'].
    destruct (IHB (A ⟨xi⟩ :: D) (up_ren xi) (ren_ok_up xi G D A Hxi)
                (inhabits (w_cons D _ _ wD dA'))) as [dB'].
    destruct (IHp D xi Hxi (inhabits wD)) as [dp'].
    exact (inhabits (t_fst D k i j _ _ _ Hik Hjk dA' dB' dp')).
  - (* t_snd *) intros G k i j A B p Hik Hjk dA IHA dB IHB dp IHp D xi Hxi [wD].
    destruct (IHA D xi Hxi (inhabits wD)) as [dA'].
    destruct (IHB (A ⟨xi⟩ :: D) (up_ren xi) (ren_ok_up xi G D A Hxi)
                (inhabits (w_cons D _ _ wD dA'))) as [dB'].
    destruct (IHp D xi Hxi (inhabits wD)) as [dp'].
    replace ((B [(fst A B p)..]) ⟨xi⟩)
      with ((B ⟨up_ren xi⟩)
              [(fst (A ⟨xi⟩) (B ⟨up_ren xi⟩) (p ⟨xi⟩))..])
      by (rasimpl; reflexivity).
    exact (inhabits (t_snd D k i j _ _ _ Hik Hjk dA' dB' dp')).
  - (* t_w *) intros G k i j A B Hik Hjk dA IHA dB IHB D xi Hxi [wD].
    destruct (IHA D xi Hxi (inhabits wD)) as [dA'].
    destruct (IHB (A ⟨xi⟩ :: D) (up_ren xi) (ren_ok_up xi G D A Hxi)
                (inhabits (w_cons D _ _ wD dA'))) as [dB'].
    exact (inhabits (t_w D k i j _ _ Hik Hjk dA' dB')).
  - (* t_sup *) intros G k i j A B a f Hik Hjk dA IHA dB IHB da IHa df IHf
      D xi Hxi [wD].
    destruct (IHA D xi Hxi (inhabits wD)) as [dA'].
    destruct (IHB (A ⟨xi⟩ :: D) (up_ren xi) (ren_ok_up xi G D A Hxi)
                (inhabits (w_cons D _ _ wD dA'))) as [dB'].
    destruct (IHa D xi Hxi (inhabits wD)) as [da'].
    destruct (IHf D xi Hxi (inhabits wD)) as [df'].
    rewrite sup_fun_ren in df'.
    exact (inhabits (t_sup D k i j _ _ _ _ Hik Hjk dA' dB' da' df')).
  - (* t_wrec *) intros G k i j m n A B C s w Hik Hjk Hjn Hmn En dA IHA dB IHB
      dC IHC dbr IHbr dih IHih ds IHs dw IHw D xi Hxi [wD].
    destruct (IHA D xi Hxi (inhabits wD)) as [dA'].
    pose proof (ren_ok_up xi G D A Hxi) as Hup1.
    pose proof (w_cons D (A ⟨xi⟩) _ wD dA') as wD1.
    destruct (IHB (A ⟨xi⟩ :: D) (up_ren xi) Hup1 (inhabits wD1)) as [dB'].
    pose proof (t_w D k i j _ _ Hik Hjk dA' dB') as dW'.
    destruct (IHC ((wt k A B) ⟨xi⟩ :: D) (up_ren xi)
                (ren_ok_up xi G D (wt k A B) Hxi)
                (inhabits (w_cons D _ _ wD dW'))) as [dC'].
    destruct (IHbr (A ⟨xi⟩ :: D) (up_ren xi) Hup1 (inhabits wD1)) as [dbr'].
    rewrite wbr_ren in dbr'.
    pose proof (w_cons _ _ _ wD1 dbr') as wD2.
    pose proof (ren_ok_up (up_ren xi) (A :: G) (A ⟨xi⟩ :: D) (wbr k A B) Hup1)
      as Hup2.
    rewrite wbr_ren in Hup2.
    destruct (IHih _ (up_ren (up_ren xi)) Hup2 (inhabits wD2)) as [dih'].
    rewrite wih_ren in dih'.
    pose proof (w_cons _ _ _ wD2 dih') as wD3.
    destruct (IHs _ (up_ren (up_ren (up_ren xi)))
                (ren_ok_wstep xi G D k n A B C Hxi) (inhabits wD3)) as [ds'].
    rewrite wsup_ty_ren in ds'.
    destruct (IHw D xi Hxi (inhabits wD)) as [dw'].
    replace ((C [w..]) ⟨xi⟩) with ((C ⟨up_ren xi⟩) [(w ⟨xi⟩)..])
      by (rasimpl; reflexivity).
    exact (inhabits (t_wrec D k i j m n _ _ _ _ _ Hik Hjk Hjn Hmn En
                      dA' dB' dC' dbr' dih' ds' dw')).
  - (* t_nat *) intros G k W IHW D xi Hxi [wD]; exact (inhabits (t_nat D k wD)).
  - (* t_zero *) intros G k W IHW D xi Hxi [wD]; exact (inhabits (t_zero D k wD)).
  - (* t_succ *) intros G k n dn IHn D xi Hxi [wD].
    destruct (IHn D xi Hxi (inhabits wD)) as [dn'].
    exact (inhabits (t_succ D _ _ dn')).
  - (* t_natrec *) intros G C z s n k j dC IHC dz IHz ds IHs dn IHn D xi Hxi [wD].
    pose proof (w_cons D (nat_ j) j wD (t_nat D j wD)) as wDn.
    destruct (IHC (nat_ j :: D) (up_ren xi) (ren_ok_up xi G D (nat_ j) Hxi)
                (inhabits wDn)) as [dC'].
    destruct (IHz D xi Hxi (inhabits wD)) as [dz'].
    destruct (IHs (C ⟨up_ren xi⟩ :: nat_ j :: D)
                (up_ren (up_ren xi))
                (ren_ok_up (up_ren xi) (nat_ j :: G) (nat_ j :: D) C
                   (ren_ok_up xi G D (nat_ j) Hxi))
                (inhabits (w_cons (nat_ j :: D) _ _ wDn dC'))) as [ds'].
    destruct (IHn D xi Hxi (inhabits wD)) as [dn'].
    replace ((C [(zero j)..]) ⟨xi⟩) with ((C ⟨up_ren xi⟩) [(zero j)..]) in dz'
      by (rasimpl; reflexivity).
    rewrite nrec_succ_ren in ds'.
    replace ((C [n..]) ⟨xi⟩) with ((C ⟨up_ren xi⟩) [(n ⟨xi⟩)..])
      by (rasimpl; reflexivity).
    exact (inhabits (t_natrec D _ _ _ _ k j dC' dz' ds' dn')).
  - (* t_prop *) intros G k W IHW D xi Hxi [wD]; exact (inhabits (t_prop D k wD)).
  - (* t_prf *) intros G k j p Hjk dp IHp D xi Hxi [wD].
    destruct (IHp D xi Hxi (inhabits wD)) as [dp'].
    exact (inhabits (t_prf D k j _ Hjk dp')).
  - (* t_all *) intros G A p j k dA IHA dp IHp D xi Hxi [wD].
    destruct (IHA D xi Hxi (inhabits wD)) as [dA'].
    destruct (IHp (A ⟨xi⟩ :: D) (up_ren xi) (ren_ok_up xi G D A Hxi)
                (inhabits (w_cons D _ _ wD dA'))) as [dp'].
    exact (inhabits (t_all D _ _ j k dA' dp')).
  - (* t_all_intro *) intros G A p t j k dA IHA dp IHp dt IHt D xi Hxi [wD].
    destruct (IHA D xi Hxi (inhabits wD)) as [dA'].
    pose proof (inhabits (w_cons D (A ⟨xi⟩) _ wD dA')) as wD'.
    destruct (IHp (A ⟨xi⟩ :: D) (up_ren xi) (ren_ok_up xi G D A Hxi) wD') as [dp'].
    destruct (IHt (A ⟨xi⟩ :: D) (up_ren xi) (ren_ok_up xi G D A Hxi) wD') as [dt'].
    exact (inhabits (t_all_intro D _ _ _ j k dA' dp' dt')).
  - (* t_all_elim *) intros G A p f u j k dA IHA dp IHp df IHf du IHu D xi Hxi [wD].
    destruct (IHA D xi Hxi (inhabits wD)) as [dA'].
    destruct (IHp (A ⟨xi⟩ :: D) (up_ren xi) (ren_ok_up xi G D A Hxi)
                (inhabits (w_cons D _ _ wD dA'))) as [dp'].
    destruct (IHf D xi Hxi (inhabits wD)) as [df'].
    destruct (IHu D xi Hxi (inhabits wD)) as [du'].
    replace ((prf j (p [u..])) ⟨xi⟩)
      with (prf j ((p ⟨up_ren xi⟩) [(u ⟨xi⟩)..])) by (rasimpl; reflexivity).
    exact (inhabits (t_all_elim D _ _ _ _ j k dA' dp' df' du')).
  - (* t_false *) intros G k W IHW D xi Hxi [wD]; exact (inhabits (t_false D k wD)).
  - (* t_absurd *) intros G T e k j dT IHT de IHe D xi Hxi [wD].
    destruct (IHT D xi Hxi (inhabits wD)) as [dT'].
    destruct (IHe D xi Hxi (inhabits wD)) as [de'].
    exact (inhabits (t_absurd D _ _ k j dT' de')).

  - (* c_refl *) intros G t A d IHd D xi Hxi [wD].
    destruct (IHd D xi Hxi (inhabits wD)) as [d'].
    exact (inhabits (c_refl D _ _ d')).
  - (* c_sym *) intros G t u A c IHc D xi Hxi [wD].
    destruct (IHc D xi Hxi (inhabits wD)) as [c'].
    exact (inhabits (c_sym D _ _ _ c')).
  - (* c_trans *) intros G t u v A c1 IH1 c2 IH2 D xi Hxi [wD].
    destruct (IH1 D xi Hxi (inhabits wD)) as [c1'].
    destruct (IH2 D xi Hxi (inhabits wD)) as [c2'].
    exact (inhabits (c_trans D _ _ _ _ c1' c2')).
  - (* c_conv *) intros G t u A B k c IHc dA IHA dB IHB cAB IHAB D xi Hxi [wD].
    destruct (IHc D xi Hxi (inhabits wD)) as [c'].
    destruct (IHA D xi Hxi (inhabits wD)) as [dA'].
    destruct (IHB D xi Hxi (inhabits wD)) as [dB'].
    destruct (IHAB D xi Hxi (inhabits wD)) as [cAB'].
    exact (inhabits (c_conv D _ _ _ _ k c' dA' dB' cAB')).
  - (* c_prf_irr *) intros G j p e e' dp IHp de IHe de' IHe' D xi Hxi [wD].
    destruct (IHp D xi Hxi (inhabits wD)) as [dp'].
    destruct (IHe D xi Hxi (inhabits wD)) as [de1].
    destruct (IHe' D xi Hxi (inhabits wD)) as [de2].
    exact (inhabits (c_prf_irr D j _ _ _ dp' de1 de2)).
  - (* c_up *) intros G j A A' dA IHA dA' IHA' c IHc D xi Hxi [wD].
    destruct (IHA D xi Hxi (inhabits wD)) as [d1].
    destruct (IHA' D xi Hxi (inhabits wD)) as [d2].
    destruct (IHc D xi Hxi (inhabits wD)) as [c'].
    exact (inhabits (c_up D j _ _ d1 d2 c')).
  - (* c_up_tm *) intros G j A t t' dA IHA dt IHt dt' IHt' c IHc D xi Hxi [wD].
    destruct (IHA D xi Hxi (inhabits wD)) as [d1].
    destruct (IHt D xi Hxi (inhabits wD)) as [d2].
    destruct (IHt' D xi Hxi (inhabits wD)) as [d3].
    destruct (IHc D xi Hxi (inhabits wD)) as [c'].
    exact (inhabits (c_up_tm D j _ _ _ d1 d2 d3 c')).
  - (* c_up_univ *) intros G k j Hjk W IHW D xi Hxi [wD].
    exact (inhabits (c_up_univ D k j Hjk wD)).
  - (* c_up_nat *) intros G k W IHW D xi Hxi [wD].
    exact (inhabits (c_up_nat D k wD)).
  - (* c_up_prop *) intros G k W IHW D xi Hxi [wD].
    exact (inhabits (c_up_prop D k wD)).
  - (* c_up_prf *) intros G k j p Hjk dp IHp D xi Hxi [wD].
    destruct (IHp D xi Hxi (inhabits wD)) as [dp'].
    exact (inhabits (c_up_prf D k j _ Hjk dp')).
  - (* c_up_pi *) intros G k i j A B Hik Hjk dA IHA dB IHB D xi Hxi [wD].
    destruct (IHA D xi Hxi (inhabits wD)) as [dA'].
    destruct (IHB (A ⟨xi⟩ :: D) (up_ren xi) (ren_ok_up xi G D A Hxi)
                (inhabits (w_cons D _ _ wD dA'))) as [dB'].
    exact (inhabits (c_up_pi D k i j _ _ Hik Hjk dA' dB')).
  - (* c_up_sig *) intros G k i j A B Hik Hjk dA IHA dB IHB D xi Hxi [wD].
    destruct (IHA D xi Hxi (inhabits wD)) as [dA'].
    destruct (IHB (A ⟨xi⟩ :: D) (up_ren xi) (ren_ok_up xi G D A Hxi)
                (inhabits (w_cons D _ _ wD dA'))) as [dB'].
    exact (inhabits (c_up_sig D k i j _ _ Hik Hjk dA' dB')).
  - (* c_up_w *) intros G k i j A B Hik Hjk dA IHA dB IHB D xi Hxi [wD].
    destruct (IHA D xi Hxi (inhabits wD)) as [dA'].
    destruct (IHB (A ⟨xi⟩ :: D) (up_ren xi) (ren_ok_up xi G D A Hxi)
                (inhabits (w_cons D _ _ wD dA'))) as [dB'].
    exact (inhabits (c_up_w D k i j _ _ Hik Hjk dA' dB')).
  - (* c_pi *) intros G k i j A A' B B' Hik Hjk dA IHA dB IHB dA' IHA' dB' IHB' cA IHcA cB IHcB
      D xi Hxi [wD].
    destruct (IHA D xi Hxi (inhabits wD)) as [d1].
    destruct (IHA' D xi Hxi (inhabits wD)) as [d3].
    destruct (IHB (A ⟨xi⟩ :: D) (up_ren xi) (ren_ok_up xi G D A Hxi)
                (inhabits (w_cons D _ _ wD d1))) as [d2].
    destruct (IHB' (A' ⟨xi⟩ :: D) (up_ren xi) (ren_ok_up xi G D A' Hxi)
                (inhabits (w_cons D _ _ wD d3))) as [d4].
    destruct (IHcA D xi Hxi (inhabits wD)) as [cA'].
    destruct (IHcB (A ⟨xi⟩ :: D) (up_ren xi) (ren_ok_up xi G D A Hxi)
                (inhabits (w_cons D _ _ wD d1))) as [cB'].
    exact (inhabits (c_pi D k i j _ _ _ _ Hik Hjk d1 d2 d3 d4 cA' cB')).
  - (* c_lam *) intros G k i j A A' B B' t t' Hik Hjk dA IHA dB IHB dA' IHA' dB' IHB'
      cA IHcA cB IHcB dt IHt dt' IHt' ct IHct D xi Hxi [wD].
    destruct (IHA D xi Hxi (inhabits wD)) as [d1].
    destruct (IHA' D xi Hxi (inhabits wD)) as [d3].
    pose proof (ren_ok_up xi G D A Hxi) as Hup.
    pose proof (ren_ok_up xi G D A' Hxi) as Hup'.
    pose proof (inhabits (w_cons D (A ⟨xi⟩) _ wD d1)) as wD1.
    pose proof (inhabits (w_cons D (A' ⟨xi⟩) _ wD d3)) as wD2.
    destruct (IHB (A ⟨xi⟩ :: D) (up_ren xi) Hup wD1) as [d2].
    destruct (IHB' (A' ⟨xi⟩ :: D) (up_ren xi) Hup' wD2) as [d4].
    destruct (IHcA D xi Hxi (inhabits wD)) as [cA'].
    destruct (IHcB (A ⟨xi⟩ :: D) (up_ren xi) Hup wD1) as [cB'].
    destruct (IHt (A ⟨xi⟩ :: D) (up_ren xi) Hup wD1) as [d5].
    destruct (IHt' (A' ⟨xi⟩ :: D) (up_ren xi) Hup' wD2) as [d6].
    destruct (IHct (A ⟨xi⟩ :: D) (up_ren xi) Hup wD1) as [ct'].
    exact (inhabits (c_lam D k i j _ _ _ _ _ _ Hik Hjk d1 d2 d3 d4 cA' cB' d5 d6 ct')).
  - (* c_app *) intros G k i j A B f f' u u' Hik Hjk dA IHA dB IHB df IHf df' IHf' cf IHcf
      du IHu du' IHu' cu IHcu D xi Hxi [wD].
    destruct (IHA D xi Hxi (inhabits wD)) as [d1].
    destruct (IHB (A ⟨xi⟩ :: D) (up_ren xi) (ren_ok_up xi G D A Hxi)
                (inhabits (w_cons D _ _ wD d1))) as [d2].
    destruct (IHf D xi Hxi (inhabits wD)) as [d3].
    destruct (IHf' D xi Hxi (inhabits wD)) as [d4].
    destruct (IHcf D xi Hxi (inhabits wD)) as [cf'].
    destruct (IHu D xi Hxi (inhabits wD)) as [d5].
    destruct (IHu' D xi Hxi (inhabits wD)) as [d6].
    destruct (IHcu D xi Hxi (inhabits wD)) as [cu'].
    replace ((B [u..]) ⟨xi⟩) with ((B ⟨up_ren xi⟩) [(u ⟨xi⟩)..])
      by (rasimpl; reflexivity).
    exact (inhabits (c_app D k i j _ _ _ _ _ _ Hik Hjk d1 d2 d3 d4 cf' d5 d6 cu')).
  - (* c_beta *) intros G k i j A B t u Hik Hjk dA IHA dB IHB dt IHt du IHu D xi Hxi [wD].
    destruct (IHA D xi Hxi (inhabits wD)) as [d1].
    pose proof (inhabits (w_cons D (A ⟨xi⟩) _ wD d1)) as wD'.
    destruct (IHB (A ⟨xi⟩ :: D) (up_ren xi) (ren_ok_up xi G D A Hxi) wD') as [d2].
    destruct (IHt (A ⟨xi⟩ :: D) (up_ren xi) (ren_ok_up xi G D A Hxi) wD') as [d3].
    destruct (IHu D xi Hxi (inhabits wD)) as [d4].
    replace ((B [u..]) ⟨xi⟩) with ((B ⟨up_ren xi⟩) [(u ⟨xi⟩)..])
      by (rasimpl; reflexivity).
    replace ((t [u..]) ⟨xi⟩) with ((t ⟨up_ren xi⟩) [(u ⟨xi⟩)..])
      by (rasimpl; reflexivity).
    exact (inhabits (c_beta D k i j _ _ _ _ Hik Hjk d1 d2 d3 d4)).
  - (* c_eta *) intros G k i j A B f Hik Hjk dA IHA dB IHB df IHf D xi Hxi [wD].
    destruct (IHA D xi Hxi (inhabits wD)) as [d1].
    destruct (IHB (A ⟨xi⟩ :: D) (up_ren xi) (ren_ok_up xi G D A Hxi)
                (inhabits (w_cons D _ _ wD d1))) as [d2].
    destruct (IHf D xi Hxi (inhabits wD)) as [d3].
    rewrite eta_ren.
    exact (inhabits (c_eta D k i j _ _ _ Hik Hjk d1 d2 d3)).
  - (* c_sig *) intros G k i j A A' B B' Hik Hjk dA IHA dB IHB dA' IHA' dB' IHB' cA IHcA cB IHcB
      D xi Hxi [wD].
    destruct (IHA D xi Hxi (inhabits wD)) as [d1].
    destruct (IHA' D xi Hxi (inhabits wD)) as [d3].
    destruct (IHB (A ⟨xi⟩ :: D) (up_ren xi) (ren_ok_up xi G D A Hxi)
                (inhabits (w_cons D _ _ wD d1))) as [d2].
    destruct (IHB' (A' ⟨xi⟩ :: D) (up_ren xi) (ren_ok_up xi G D A' Hxi)
                (inhabits (w_cons D _ _ wD d3))) as [d4].
    destruct (IHcA D xi Hxi (inhabits wD)) as [cA'].
    destruct (IHcB (A ⟨xi⟩ :: D) (up_ren xi) (ren_ok_up xi G D A Hxi)
                (inhabits (w_cons D _ _ wD d1))) as [cB'].
    exact (inhabits (c_sig D k i j _ _ _ _ Hik Hjk d1 d2 d3 d4 cA' cB')).
  - (* c_pair *) intros G k i j A B t t' u u' Hik Hjk dA IHA dB IHB dt IHt dt' IHt' ct IHct
      du IHu du' IHu' cu IHcu D xi Hxi [wD].
    destruct (IHA D xi Hxi (inhabits wD)) as [d1].
    destruct (IHB (A ⟨xi⟩ :: D) (up_ren xi) (ren_ok_up xi G D A Hxi)
                (inhabits (w_cons D _ _ wD d1))) as [d2].
    destruct (IHt D xi Hxi (inhabits wD)) as [d3].
    destruct (IHt' D xi Hxi (inhabits wD)) as [d4].
    destruct (IHct D xi Hxi (inhabits wD)) as [ct'].
    destruct (IHu D xi Hxi (inhabits wD)) as [d5].
    destruct (IHu' D xi Hxi (inhabits wD)) as [d6].
    destruct (IHcu D xi Hxi (inhabits wD)) as [cu'].
    replace ((B [t..]) ⟨xi⟩) with ((B ⟨up_ren xi⟩) [(t ⟨xi⟩)..]) in d5, d6, cu'
      by (rasimpl; reflexivity).
    exact (inhabits (c_pair D k i j _ _ _ _ _ _ Hik Hjk d1 d2 d3 d4 ct' d5 d6 cu')).
  - (* c_fst *) intros G k i j A B p p' Hik Hjk dA IHA dB IHB dp IHp dp' IHp' cp IHcp
      D xi Hxi [wD].
    destruct (IHA D xi Hxi (inhabits wD)) as [d1].
    destruct (IHB (A ⟨xi⟩ :: D) (up_ren xi) (ren_ok_up xi G D A Hxi)
                (inhabits (w_cons D _ _ wD d1))) as [d2].
    destruct (IHp D xi Hxi (inhabits wD)) as [d3].
    destruct (IHp' D xi Hxi (inhabits wD)) as [d4].
    destruct (IHcp D xi Hxi (inhabits wD)) as [cp'].
    exact (inhabits (c_fst D k i j _ _ _ _ Hik Hjk d1 d2 d3 d4 cp')).
  - (* c_snd *) intros G k i j A B p p' Hik Hjk dA IHA dB IHB dp IHp dp' IHp' cp IHcp
      D xi Hxi [wD].
    destruct (IHA D xi Hxi (inhabits wD)) as [d1].
    destruct (IHB (A ⟨xi⟩ :: D) (up_ren xi) (ren_ok_up xi G D A Hxi)
                (inhabits (w_cons D _ _ wD d1))) as [d2].
    destruct (IHp D xi Hxi (inhabits wD)) as [d3].
    destruct (IHp' D xi Hxi (inhabits wD)) as [d4].
    destruct (IHcp D xi Hxi (inhabits wD)) as [cp'].
    replace ((B [(fst A B p)..]) ⟨xi⟩)
      with ((B ⟨up_ren xi⟩)
              [(fst (A ⟨xi⟩) (B ⟨up_ren xi⟩) (p ⟨xi⟩))..])
      by (rasimpl; reflexivity).
    exact (inhabits (c_snd D k i j _ _ _ _ Hik Hjk d1 d2 d3 d4 cp')).
  - (* c_fst_beta *) intros G k i j A B t u Hik Hjk dA IHA dB IHB dt IHt du IHu D xi Hxi [wD].
    destruct (IHA D xi Hxi (inhabits wD)) as [d1].
    destruct (IHB (A ⟨xi⟩ :: D) (up_ren xi) (ren_ok_up xi G D A Hxi)
                (inhabits (w_cons D _ _ wD d1))) as [d2].
    destruct (IHt D xi Hxi (inhabits wD)) as [d3].
    destruct (IHu D xi Hxi (inhabits wD)) as [d4].
    replace ((B [t..]) ⟨xi⟩) with ((B ⟨up_ren xi⟩) [(t ⟨xi⟩)..]) in d4
      by (rasimpl; reflexivity).
    exact (inhabits (c_fst_beta D k i j _ _ _ _ Hik Hjk d1 d2 d3 d4)).
  - (* c_snd_beta *) intros G k i j A B t u Hik Hjk dA IHA dB IHB dt IHt du IHu D xi Hxi [wD].
    destruct (IHA D xi Hxi (inhabits wD)) as [d1].
    destruct (IHB (A ⟨xi⟩ :: D) (up_ren xi) (ren_ok_up xi G D A Hxi)
                (inhabits (w_cons D _ _ wD d1))) as [d2].
    destruct (IHt D xi Hxi (inhabits wD)) as [d3].
    destruct (IHu D xi Hxi (inhabits wD)) as [d4].
    replace ((B [t..]) ⟨xi⟩) with ((B ⟨up_ren xi⟩) [(t ⟨xi⟩)..]) in d4 |- *
      by (rasimpl; reflexivity).
    exact (inhabits (c_snd_beta D k i j _ _ _ _ Hik Hjk d1 d2 d3 d4)).
  - (* c_surj *) intros G k i j A B p Hik Hjk dA IHA dB IHB dp IHp D xi Hxi [wD].
    destruct (IHA D xi Hxi (inhabits wD)) as [d1].
    destruct (IHB (A ⟨xi⟩ :: D) (up_ren xi) (ren_ok_up xi G D A Hxi)
                (inhabits (w_cons D _ _ wD d1))) as [d2].
    destruct (IHp D xi Hxi (inhabits wD)) as [d3].
    exact (inhabits (c_surj D k i j _ _ _ Hik Hjk d1 d2 d3)).
  - (* c_w *) intros G k i j A A' B B' Hik Hjk dA IHA dB IHB dA' IHA' dB' IHB'
      cA IHcA cB IHcB D xi Hxi [wD].
    destruct (IHA D xi Hxi (inhabits wD)) as [d1].
    destruct (IHA' D xi Hxi (inhabits wD)) as [d3].
    destruct (IHB (A ⟨xi⟩ :: D) (up_ren xi) (ren_ok_up xi G D A Hxi)
                (inhabits (w_cons D _ _ wD d1))) as [d2].
    destruct (IHB' (A' ⟨xi⟩ :: D) (up_ren xi) (ren_ok_up xi G D A' Hxi)
                (inhabits (w_cons D _ _ wD d3))) as [d4].
    destruct (IHcA D xi Hxi (inhabits wD)) as [cA'].
    destruct (IHcB (A ⟨xi⟩ :: D) (up_ren xi) (ren_ok_up xi G D A Hxi)
                (inhabits (w_cons D _ _ wD d1))) as [cB'].
    exact (inhabits (c_w D k i j _ _ _ _ Hik Hjk d1 d2 d3 d4 cA' cB')).
  - (* c_sup *) intros G k i j A B a a' f f' Hik Hjk dA IHA dB IHB
      da IHa da' IHa' ca IHca df IHf df' IHf' cf IHcf D xi Hxi [wD].
    destruct (IHA D xi Hxi (inhabits wD)) as [dA'].
    destruct (IHB (A ⟨xi⟩ :: D) (up_ren xi) (ren_ok_up xi G D A Hxi)
                (inhabits (w_cons D _ _ wD dA'))) as [dB'].
    destruct (IHa D xi Hxi (inhabits wD)) as [d1].
    destruct (IHa' D xi Hxi (inhabits wD)) as [d2].
    destruct (IHca D xi Hxi (inhabits wD)) as [c1].
    destruct (IHf D xi Hxi (inhabits wD)) as [d3].
    destruct (IHf' D xi Hxi (inhabits wD)) as [d4].
    destruct (IHcf D xi Hxi (inhabits wD)) as [c2].
    rewrite sup_fun_ren in d3, d4, c2.
    exact (inhabits (c_sup D k i j _ _ _ _ _ _ Hik Hjk dA' dB'
                      d1 d2 c1 d3 d4 c2)).
  - (* c_wrec *) intros G k i j m n A B C C' s s' w w' Hik Hjk Hjn Hmn En
      dA IHA dB IHB dC IHC dC' IHC' cC IHcC dbr IHbr dih IHih
      ds IHs ds' IHs' cs IHcs dw IHw dw' IHw' cw IHcw D xi Hxi [wD].
    destruct (IHA D xi Hxi (inhabits wD)) as [dA1].
    pose proof (ren_ok_up xi G D A Hxi) as Hup1.
    pose proof (w_cons D (A ⟨xi⟩) _ wD dA1) as wD1.
    destruct (IHB (A ⟨xi⟩ :: D) (up_ren xi) Hup1 (inhabits wD1)) as [dB1].
    pose proof (t_w D k i j _ _ Hik Hjk dA1 dB1) as dW1.
    pose proof (ren_ok_up xi G D (wt k A B) Hxi) as HupW.
    pose proof (inhabits (w_cons D _ _ wD dW1)) as wDW.
    destruct (IHC ((wt k A B) ⟨xi⟩ :: D) (up_ren xi) HupW wDW) as [dC1].
    destruct (IHC' ((wt k A B) ⟨xi⟩ :: D) (up_ren xi) HupW wDW) as [dC2].
    destruct (IHcC ((wt k A B) ⟨xi⟩ :: D) (up_ren xi) HupW wDW) as [cC1].
    destruct (IHbr (A ⟨xi⟩ :: D) (up_ren xi) Hup1 (inhabits wD1)) as [dbr1].
    rewrite wbr_ren in dbr1.
    pose proof (w_cons _ _ _ wD1 dbr1) as wD2.
    pose proof (ren_ok_up (up_ren xi) (A :: G) (A ⟨xi⟩ :: D) (wbr k A B) Hup1)
      as Hup2.
    rewrite wbr_ren in Hup2.
    destruct (IHih _ (up_ren (up_ren xi)) Hup2 (inhabits wD2)) as [dih1].
    rewrite wih_ren in dih1.
    pose proof (w_cons _ _ _ wD2 dih1) as wD3.
    pose proof (ren_ok_wstep xi G D k n A B C Hxi) as Hup3.
    destruct (IHs _ (up_ren (up_ren (up_ren xi))) Hup3 (inhabits wD3)) as [ds1].
    destruct (IHs' _ (up_ren (up_ren (up_ren xi))) Hup3 (inhabits wD3)) as [ds2].
    destruct (IHcs _ (up_ren (up_ren (up_ren xi))) Hup3 (inhabits wD3)) as [cs1].
    rewrite wsup_ty_ren in ds1, ds2, cs1.
    destruct (IHw D xi Hxi (inhabits wD)) as [dw1].
    destruct (IHw' D xi Hxi (inhabits wD)) as [dw2].
    destruct (IHcw D xi Hxi (inhabits wD)) as [cw1].
    replace ((C [w..]) ⟨xi⟩) with ((C ⟨up_ren xi⟩) [(w ⟨xi⟩)..])
      by (rasimpl; reflexivity).
    exact (inhabits (c_wrec D k i j m n _ _ _ _ _ _ _ _ Hik Hjk Hjn Hmn En
                      dA1 dB1 dC1 dC2 cC1 dbr1 dih1 ds1 ds2 cs1 dw1 dw2 cw1)).
  - (* c_wrec_sup *) intros G k i j m n A B C s a f Hik Hjk Hjn Hmn En
      dA IHA dB IHB dC IHC dbr IHbr dih IHih ds IHs da IHa df IHf
      D xi Hxi [wD].
    destruct (IHA D xi Hxi (inhabits wD)) as [dA1].
    pose proof (ren_ok_up xi G D A Hxi) as Hup1.
    pose proof (w_cons D (A ⟨xi⟩) _ wD dA1) as wD1.
    destruct (IHB (A ⟨xi⟩ :: D) (up_ren xi) Hup1 (inhabits wD1)) as [dB1].
    pose proof (t_w D k i j _ _ Hik Hjk dA1 dB1) as dW1.
    destruct (IHC ((wt k A B) ⟨xi⟩ :: D) (up_ren xi)
                (ren_ok_up xi G D (wt k A B) Hxi)
                (inhabits (w_cons D _ _ wD dW1))) as [dC1].
    destruct (IHbr (A ⟨xi⟩ :: D) (up_ren xi) Hup1 (inhabits wD1)) as [dbr1].
    rewrite wbr_ren in dbr1.
    pose proof (w_cons _ _ _ wD1 dbr1) as wD2.
    pose proof (ren_ok_up (up_ren xi) (A :: G) (A ⟨xi⟩ :: D) (wbr k A B) Hup1)
      as Hup2.
    rewrite wbr_ren in Hup2.
    destruct (IHih _ (up_ren (up_ren xi)) Hup2 (inhabits wD2)) as [dih1].
    rewrite wih_ren in dih1.
    pose proof (w_cons _ _ _ wD2 dih1) as wD3.
    destruct (IHs _ (up_ren (up_ren (up_ren xi)))
                (ren_ok_wstep xi G D k n A B C Hxi) (inhabits wD3)) as [ds1].
    rewrite wsup_ty_ren in ds1.
    destruct (IHa D xi Hxi (inhabits wD)) as [da1].
    destruct (IHf D xi Hxi (inhabits wD)) as [df1].
    rewrite sup_fun_ren in df1.
    (* the contractum, and the type of the redex *)
    rewrite wrec_sup_contractum_ren.
    replace ((C [(sup k A B a f)..]) ⟨xi⟩)
      with ((C ⟨up_ren xi⟩)
              [(sup k (A ⟨xi⟩) (B ⟨up_ren xi⟩) (a ⟨xi⟩) (f ⟨xi⟩))..])
      by (rasimpl; reflexivity).
    exact (inhabits (c_wrec_sup D k i j m n _ _ _ _ _ _ Hik Hjk Hjn Hmn En
                      dA1 dB1 dC1 dbr1 dih1 ds1 da1 df1)).
  - (* c_succ *) intros G k n n' dn IHn dn' IHn' cn IHcn D xi Hxi [wD].
    destruct (IHn D xi Hxi (inhabits wD)) as [d1].
    destruct (IHn' D xi Hxi (inhabits wD)) as [d2].
    destruct (IHcn D xi Hxi (inhabits wD)) as [c'].
    exact (inhabits (c_succ D _ _ _ d1 d2 c')).
  - (* c_natrec *) intros G C C' z z' s s' n n' k j dC IHC dC' IHC' cC IHcC
      dz IHz dz' IHz' cz IHcz ds IHs ds' IHs' cs IHcs dn IHn dn' IHn' cn IHcn
      D xi Hxi [wD].
    pose proof (w_cons D (nat_ j) j wD (t_nat D j wD)) as wDn.
    pose proof (ren_ok_up xi G D (nat_ j) Hxi) as Hxi1.
    destruct (IHC (nat_ j :: D) (up_ren xi) Hxi1 (inhabits wDn)) as [d1].
    destruct (IHC' (nat_ j :: D) (up_ren xi) Hxi1 (inhabits wDn)) as [d2].
    destruct (IHcC (nat_ j :: D) (up_ren xi) Hxi1 (inhabits wDn)) as [cC'].
    destruct (IHz D xi Hxi (inhabits wD)) as [d3].
    destruct (IHz' D xi Hxi (inhabits wD)) as [d4].
    destruct (IHcz D xi Hxi (inhabits wD)) as [cz'].
    pose proof (ren_ok_up (up_ren xi) (nat_ j :: G) (nat_ j :: D) C Hxi1) as Hxi2.
    pose proof (inhabits (w_cons (nat_ j :: D) (C ⟨up_ren xi⟩) _ wDn d1)) as wDc.
    destruct (IHs (C ⟨up_ren xi⟩ :: nat_ j :: D)
                (up_ren (up_ren xi)) Hxi2 wDc) as [d5].
    destruct (IHs' (C ⟨up_ren xi⟩ :: nat_ j :: D)
                (up_ren (up_ren xi)) Hxi2 wDc) as [d6].
    destruct (IHcs (C ⟨up_ren xi⟩ :: nat_ j :: D)
                (up_ren (up_ren xi)) Hxi2 wDc) as [cs'].
    destruct (IHn D xi Hxi (inhabits wD)) as [d7].
    destruct (IHn' D xi Hxi (inhabits wD)) as [d8].
    destruct (IHcn D xi Hxi (inhabits wD)) as [cn'].
    replace ((C [(zero j)..]) ⟨xi⟩) with ((C ⟨up_ren xi⟩) [(zero j)..]) in d3, d4, cz'
      by (rasimpl; reflexivity).
    rewrite nrec_succ_ren in d5, d6, cs'.
    replace ((C [n..]) ⟨xi⟩) with ((C ⟨up_ren xi⟩) [(n ⟨xi⟩)..])
      by (rasimpl; reflexivity).
    exact (inhabits (c_natrec D _ _ _ _ _ _ _ _ k j d1 d2 cC' d3 d4 cz'
                       d5 d6 cs' d7 d8 cn')).
  - (* c_rec_zero *) intros G C z s k j dC IHC dz IHz ds IHs D xi Hxi [wD].
    pose proof (w_cons D (nat_ j) j wD (t_nat D j wD)) as wDn.
    pose proof (ren_ok_up xi G D (nat_ j) Hxi) as Hxi1.
    destruct (IHC (nat_ j :: D) (up_ren xi) Hxi1 (inhabits wDn)) as [d1].
    destruct (IHz D xi Hxi (inhabits wD)) as [d2].
    destruct (IHs (C ⟨up_ren xi⟩ :: nat_ j :: D)
                (up_ren (up_ren xi))
                (ren_ok_up (up_ren xi) (nat_ j :: G) (nat_ j :: D) C Hxi1)
                (inhabits (w_cons (nat_ j :: D) _ _ wDn d1))) as [d3].
    rewrite nrec_succ_ren in d3.
    replace ((C [(zero j)..]) ⟨xi⟩) with ((C ⟨up_ren xi⟩) [(zero j)..]) in d2 |- *
      by (rasimpl; reflexivity).
    exact (inhabits (c_rec_zero D _ _ _ k j d1 d2 d3)).
  - (* c_rec_succ *) intros G C z s n k j dC IHC dz IHz ds IHs dn IHn D xi Hxi [wD].
    pose proof (w_cons D (nat_ j) j wD (t_nat D j wD)) as wDn.
    pose proof (ren_ok_up xi G D (nat_ j) Hxi) as Hxi1.
    destruct (IHC (nat_ j :: D) (up_ren xi) Hxi1 (inhabits wDn)) as [d1].
    destruct (IHz D xi Hxi (inhabits wD)) as [d2].
    destruct (IHs (C ⟨up_ren xi⟩ :: nat_ j :: D)
                (up_ren (up_ren xi))
                (ren_ok_up (up_ren xi) (nat_ j :: G) (nat_ j :: D) C Hxi1)
                (inhabits (w_cons (nat_ j :: D) _ _ wDn d1))) as [d3].
    destruct (IHn D xi Hxi (inhabits wD)) as [d4].
    rewrite nrec_succ_ren in d3.
    replace ((C [(zero j)..]) ⟨xi⟩) with ((C ⟨up_ren xi⟩) [(zero j)..]) in d2
      by (rasimpl; reflexivity).
    rewrite rec_succ_ren.
    replace ((C [(succ n)..]) ⟨xi⟩)
      with ((C ⟨up_ren xi⟩) [(succ (n ⟨xi⟩))..]) by (rasimpl; reflexivity).
    exact (inhabits (c_rec_succ D _ _ _ _ k j d1 d2 d3 d4)).
  - (* c_prf *) intros G k j p p' Hjk dp IHp dp' IHp' c IHc D xi Hxi [wD].
    destruct (IHp D xi Hxi (inhabits wD)) as [d1].
    destruct (IHp' D xi Hxi (inhabits wD)) as [d2].
    destruct (IHc D xi Hxi (inhabits wD)) as [c'].
    exact (inhabits (c_prf D k j _ _ Hjk d1 d2 c')).
  - (* c_all *) intros G A A' p p' j k dA IHA dp IHp dA' IHA' dp' IHp' cA IHcA cp IHcp
      D xi Hxi [wD].
    destruct (IHA D xi Hxi (inhabits wD)) as [d1].
    destruct (IHA' D xi Hxi (inhabits wD)) as [d3].
    destruct (IHp (A ⟨xi⟩ :: D) (up_ren xi) (ren_ok_up xi G D A Hxi)
                (inhabits (w_cons D _ _ wD d1))) as [d2].
    destruct (IHp' (A' ⟨xi⟩ :: D) (up_ren xi) (ren_ok_up xi G D A' Hxi)
                (inhabits (w_cons D _ _ wD d3))) as [d4].
    destruct (IHcA D xi Hxi (inhabits wD)) as [cA'].
    destruct (IHcp (A ⟨xi⟩ :: D) (up_ren xi) (ren_ok_up xi G D A Hxi)
                (inhabits (w_cons D _ _ wD d1))) as [cp'].
    exact (inhabits (c_all D _ _ _ _ j k d1 d2 d3 d4 cA' cp')).
Qed.

Corollary ty_ren G t A (d : ty G t A) D xi :
  ren_ok xi G D -> inhabited (wfc D) -> inhabited (ty D (t ⟨xi⟩) (A ⟨xi⟩)).
Proof. exact (proj1 (proj2 renaming) G t A d D xi). Qed.

Corollary cv_ren G t u A (c : cv G t u A) D xi :
  ren_ok xi G D -> inhabited (wfc D) ->
  inhabited (cv D (t ⟨xi⟩) (u ⟨xi⟩) (A ⟨xi⟩)).
Proof. exact (proj2 (proj2 renaming) G t u A c D xi). Qed.

(* ---- substitution ---- *)

Definition sub_ok (sigma : nat -> tm) (G D : ctx) : Prop :=
  forall i A, lookup i G A -> inhabited (ty D (sigma i) (A [sigma])).

Lemma sub_ok_up sigma G D A k (wD : wfc D) (dA : ty D (A [sigma]) (UU k))
  (H : sub_ok sigma G D) :
  sub_ok (up_subst sigma) (A :: G) (A [sigma] :: D).
Proof.
  intros i B HB; inversion HB; subst.
  - replace ((A ⟨↑⟩) [up_subst sigma]) with ((A [sigma]) ⟨↑⟩)
      by (rasimpl; reflexivity).
    exact (inhabits (t_var (A [sigma] :: D) 0 ((A [sigma]) ⟨↑⟩)
                       (w_cons D (A [sigma]) _ wD dA)
                       (lookup_O D (A [sigma])))).
  - match goal with
    | H0 : lookup ?i0 G ?A0 |- _ =>
        replace ((A0 ⟨↑⟩) [up_subst sigma]) with ((A0 [sigma]) ⟨↑⟩)
          by (rasimpl; reflexivity);
        destruct (H i0 A0 H0) as [d];
        exact (ty_ren D (sigma i0) (A0 [sigma]) d (A [sigma] :: D) ↑
                 (ren_ok_shift D (A [sigma]))
                 (inhabits (w_cons D (A [sigma]) _ wD dA)))
    end.
Qed.

(* the same plumbing for substitutions *)
Lemma sub_ok_wstep sigma G D k n i A B C (wD : wfc D)
  (dA : ty D (A [sigma]) (UU i))
  (dbr : ty (A [sigma] :: D) (wbr k (A [sigma]) (B [up_subst sigma])) (UU k))
  (dih : ty (wbr k (A [sigma]) (B [up_subst sigma]) :: A [sigma] :: D)
            (wih n k (A [sigma]) (B [up_subst sigma]) (C [up_subst sigma])) (UU n))
  (H : sub_ok sigma G D) :
  sub_ok (up_subst (up_subst (up_subst sigma)))
    (wih n k A B C :: wbr k A B :: A :: G)
    (wih n k (A [sigma]) (B [up_subst sigma]) (C [up_subst sigma])
       :: wbr k (A [sigma]) (B [up_subst sigma]) :: A [sigma] :: D).
Proof.
  rewrite <- wbr_subst in dbr.
  rewrite <- wih_subst in dih.
  (* the wbr also has to go back in dih's CONTEXT, not only in its type *)
  rewrite <- wbr_subst in dih.
  pose proof (sub_ok_up sigma G D A i wD dA H) as H1.
  pose proof (w_cons D _ _ wD dA) as wD1.
  pose proof (sub_ok_up (up_subst sigma) (A :: G) (A [sigma] :: D)
                (wbr k A B) k wD1 dbr H1) as H2.
  pose proof (w_cons _ _ _ wD1 dbr) as wD2.
  pose proof (sub_ok_up (up_subst (up_subst sigma)) (wbr k A B :: A :: G) _
                (wih n k A B C) n wD2 dih H2) as H3.
  rewrite wbr_subst, wih_subst in H3.
  exact H3.
Qed.

Theorem substitution :
  (forall G, wfc G -> True)
  /\ (forall G t A, ty G t A -> forall D sigma, sub_ok sigma G D -> inhabited (wfc D) ->
        inhabited (ty D (t [sigma]) (A [sigma])))
  /\ (forall G t u A, cv G t u A -> forall D sigma, sub_ok sigma G D -> inhabited (wfc D) ->
        inhabited (cv D (t [sigma]) (u [sigma]) (A [sigma]))).
Proof.
  apply wty_min.
  - (* w_nil *) exact I.
  - (* w_cons *) intros; exact I.
  - (* t_var *) intros G i A W IHW Hl D sigma Hs [wD]; exact (Hs i A Hl).
  - (* t_conv *) intros G t A B k dt IHt dA IHA dB IHB c IHc D sigma Hs [wD].
    destruct (IHt D sigma Hs (inhabits wD)) as [dt'].
    destruct (IHA D sigma Hs (inhabits wD)) as [dA'].
    destruct (IHB D sigma Hs (inhabits wD)) as [dB'].
    destruct (IHc D sigma Hs (inhabits wD)) as [c'].
    exact (inhabits (t_conv D _ _ _ k dt' dA' dB' c')).
  - (* t_univ *) intros G k j Hjk W IHW D sigma Hs [wD]; exact (inhabits (t_univ D k j Hjk wD)).
  - (* t_up *) intros G j A dA IHA D sigma Hs [wD].
    destruct (IHA D sigma Hs (inhabits wD)) as [dA'].
    exact (inhabits (t_up D j _ dA')).
  - (* t_up_tm *) intros G j A t dA IHA dt IHt D sigma Hs [wD].
    destruct (IHA D sigma Hs (inhabits wD)) as [dA'].
    destruct (IHt D sigma Hs (inhabits wD)) as [dt'].
    exact (inhabits (t_up_tm D j _ _ dA' dt')).
  - (* t_pi *) intros G k i j A B Hik Hjk dA IHA dB IHB D sigma Hs [wD].
    destruct (IHA D sigma Hs (inhabits wD)) as [dA'].
    destruct (IHB (A [sigma] :: D) (up_subst sigma) (sub_ok_up sigma G D A _ wD dA' Hs)
                (inhabits (w_cons D _ _ wD dA'))) as [dB'].
    exact (inhabits (t_pi D k i j _ _ Hik Hjk dA' dB')).
  - (* t_lam *) intros G k i j A B t Hik Hjk dA IHA dB IHB dt IHt D sigma Hs [wD].
    destruct (IHA D sigma Hs (inhabits wD)) as [dA'].
    pose proof (sub_ok_up sigma G D A _ wD dA' Hs) as Hs1.
    pose proof (inhabits (w_cons D (A [sigma]) _ wD dA')) as wD'.
    destruct (IHB (A [sigma] :: D) (up_subst sigma) Hs1 wD') as [dB'].
    destruct (IHt (A [sigma] :: D) (up_subst sigma) Hs1 wD') as [dt'].
    exact (inhabits (t_lam D k i j _ _ _ Hik Hjk dA' dB' dt')).
  - (* t_app *) intros G k i j A B f u Hik Hjk dA IHA dB IHB df IHf du IHu D sigma Hs [wD].
    destruct (IHA D sigma Hs (inhabits wD)) as [dA'].
    destruct (IHB (A [sigma] :: D) (up_subst sigma) (sub_ok_up sigma G D A _ wD dA' Hs)
                (inhabits (w_cons D _ _ wD dA'))) as [dB'].
    destruct (IHf D sigma Hs (inhabits wD)) as [df'].
    destruct (IHu D sigma Hs (inhabits wD)) as [du'].
    replace ((B [u..]) [sigma]) with ((B [up_subst sigma]) [(u [sigma])..])
      by (rasimpl; reflexivity).
    exact (inhabits (t_app D k i j _ _ _ _ Hik Hjk dA' dB' df' du')).
  - (* t_sig *) intros G k i j A B Hik Hjk dA IHA dB IHB D sigma Hs [wD].
    destruct (IHA D sigma Hs (inhabits wD)) as [dA'].
    destruct (IHB (A [sigma] :: D) (up_subst sigma) (sub_ok_up sigma G D A _ wD dA' Hs)
                (inhabits (w_cons D _ _ wD dA'))) as [dB'].
    exact (inhabits (t_sig D k i j _ _ Hik Hjk dA' dB')).
  - (* t_pair *) intros G k i j A B t u Hik Hjk dA IHA dB IHB dt IHt du IHu D sigma Hs [wD].
    destruct (IHA D sigma Hs (inhabits wD)) as [dA'].
    destruct (IHB (A [sigma] :: D) (up_subst sigma) (sub_ok_up sigma G D A _ wD dA' Hs)
                (inhabits (w_cons D _ _ wD dA'))) as [dB'].
    destruct (IHt D sigma Hs (inhabits wD)) as [dt'].
    destruct (IHu D sigma Hs (inhabits wD)) as [du'].
    replace ((B [t..]) [sigma]) with ((B [up_subst sigma]) [(t [sigma])..]) in du'
      by (rasimpl; reflexivity).
    exact (inhabits (t_pair D k i j _ _ _ _ Hik Hjk dA' dB' dt' du')).
  - (* t_fst *) intros G k i j A B p Hik Hjk dA IHA dB IHB dp IHp D sigma Hs [wD].
    destruct (IHA D sigma Hs (inhabits wD)) as [dA'].
    destruct (IHB (A [sigma] :: D) (up_subst sigma) (sub_ok_up sigma G D A _ wD dA' Hs)
                (inhabits (w_cons D _ _ wD dA'))) as [dB'].
    destruct (IHp D sigma Hs (inhabits wD)) as [dp'].
    exact (inhabits (t_fst D k i j _ _ _ Hik Hjk dA' dB' dp')).
  - (* t_snd *) intros G k i j A B p Hik Hjk dA IHA dB IHB dp IHp D sigma Hs [wD].
    destruct (IHA D sigma Hs (inhabits wD)) as [dA'].
    destruct (IHB (A [sigma] :: D) (up_subst sigma) (sub_ok_up sigma G D A _ wD dA' Hs)
                (inhabits (w_cons D _ _ wD dA'))) as [dB'].
    destruct (IHp D sigma Hs (inhabits wD)) as [dp'].
    replace ((B [(fst A B p)..]) [sigma])
      with ((B [up_subst sigma])
              [(fst (A [sigma]) (B [up_subst sigma]) (p [sigma]))..])
      by (rasimpl; reflexivity).
    exact (inhabits (t_snd D k i j _ _ _ Hik Hjk dA' dB' dp')).
  - (* t_w *) intros G k i j A B Hik Hjk dA IHA dB IHB D sigma Hs [wD].
    destruct (IHA D sigma Hs (inhabits wD)) as [dA'].
    destruct (IHB (A [sigma] :: D) (up_subst sigma)
                (sub_ok_up sigma G D A _ wD dA' Hs)
                (inhabits (w_cons D _ _ wD dA'))) as [dB'].
    exact (inhabits (t_w D k i j _ _ Hik Hjk dA' dB')).
  - (* t_sup *) intros G k i j A B a f Hik Hjk dA IHA dB IHB da IHa df IHf
      D sigma Hs [wD].
    destruct (IHA D sigma Hs (inhabits wD)) as [dA'].
    destruct (IHB (A [sigma] :: D) (up_subst sigma)
                (sub_ok_up sigma G D A _ wD dA' Hs)
                (inhabits (w_cons D _ _ wD dA'))) as [dB'].
    destruct (IHa D sigma Hs (inhabits wD)) as [da'].
    destruct (IHf D sigma Hs (inhabits wD)) as [df'].
    rewrite sup_fun_subst in df'.
    exact (inhabits (t_sup D k i j _ _ _ _ Hik Hjk dA' dB' da' df')).
  - (* t_wrec *) intros G k i j m n A B C s w Hik Hjk Hjn Hmn En dA IHA dB IHB
      dC IHC dbr IHbr dih IHih ds IHs dw IHw D sigma Hs [wD].
    destruct (IHA D sigma Hs (inhabits wD)) as [dA'].
    pose proof (sub_ok_up sigma G D A _ wD dA' Hs) as Hup1.
    pose proof (w_cons D (A [sigma]) _ wD dA') as wD1.
    destruct (IHB (A [sigma] :: D) (up_subst sigma) Hup1 (inhabits wD1)) as [dB'].
    pose proof (t_w D k i j _ _ Hik Hjk dA' dB') as dW'.
    destruct (IHC ((wt k A B) [sigma] :: D) (up_subst sigma)
                (sub_ok_up sigma G D (wt k A B) _ wD dW' Hs)
                (inhabits (w_cons D _ _ wD dW'))) as [dC'].
    destruct (IHbr (A [sigma] :: D) (up_subst sigma) Hup1 (inhabits wD1)) as [dbr'].
    rewrite wbr_subst in dbr'.
    pose proof (w_cons _ _ _ wD1 dbr') as wD2.
    pose proof (sub_ok_up (up_subst sigma) (A :: G) (A [sigma] :: D)
                  (wbr k A B) _ wD1 (eq_rect _ (fun X => ty _ X _) dbr' _
                     (eq_sym (wbr_subst k A B sigma))) Hup1) as Hup2.
    rewrite wbr_subst in Hup2.
    destruct (IHih _ (up_subst (up_subst sigma)) Hup2 (inhabits wD2)) as [dih'].
    rewrite wih_subst in dih'.
    pose proof (w_cons _ _ _ wD2 dih') as wD3.
    destruct (IHs _ (up_subst (up_subst (up_subst sigma)))
                (sub_ok_wstep sigma G D k n i A B C wD dA' dbr' dih' Hs)
                (inhabits wD3)) as [ds'].
    rewrite wsup_ty_subst in ds'.
    destruct (IHw D sigma Hs (inhabits wD)) as [dw'].
    replace ((C [w..]) [sigma]) with ((C [up_subst sigma]) [(w [sigma])..])
      by (rasimpl; reflexivity).
    exact (inhabits (t_wrec D k i j m n _ _ _ _ _ Hik Hjk Hjn Hmn En
                      dA' dB' dC' dbr' dih' ds' dw')).
  - (* t_nat *) intros G k W IHW D sigma Hs [wD]; exact (inhabits (t_nat D k wD)).
  - (* t_zero *) intros G k W IHW D sigma Hs [wD]; exact (inhabits (t_zero D k wD)).
  - (* t_succ *) intros G k n dn IHn D sigma Hs [wD].
    destruct (IHn D sigma Hs (inhabits wD)) as [dn'].
    exact (inhabits (t_succ D _ _ dn')).
  - (* t_natrec *) intros G C z s n k j dC IHC dz IHz ds IHs dn IHn D sigma Hs [wD].
    pose proof (w_cons D (nat_ j) j wD (t_nat D j wD)) as wDn.
    pose proof (sub_ok_up sigma G D (nat_ j) j wD (t_nat D j wD) Hs) as Hs1.
    destruct (IHC (nat_ j :: D) (up_subst sigma) Hs1 (inhabits wDn)) as [dC'].
    destruct (IHz D sigma Hs (inhabits wD)) as [dz'].
    destruct (IHs (C [up_subst sigma] :: nat_ j :: D) (up_subst (up_subst sigma))
                (sub_ok_up (up_subst sigma) (nat_ j :: G) (nat_ j :: D) C _ wDn dC' Hs1)
                (inhabits (w_cons (nat_ j :: D) _ _ wDn dC'))) as [ds'].
    destruct (IHn D sigma Hs (inhabits wD)) as [dn'].
    replace ((C [(zero j)..]) [sigma]) with ((C [up_subst sigma]) [(zero j)..]) in dz'
      by (rasimpl; reflexivity).
    rewrite nrec_succ_subst in ds'.
    replace ((C [n..]) [sigma]) with ((C [up_subst sigma]) [(n [sigma])..])
      by (rasimpl; reflexivity).
    exact (inhabits (t_natrec D _ _ _ _ k j dC' dz' ds' dn')).
  - (* t_prop *) intros G k W IHW D sigma Hs [wD]; exact (inhabits (t_prop D k wD)).
  - (* t_prf *) intros G k j p Hjk dp IHp D sigma Hs [wD].
    destruct (IHp D sigma Hs (inhabits wD)) as [dp'].
    exact (inhabits (t_prf D k j _ Hjk dp')).
  - (* t_all *) intros G A p j k dA IHA dp IHp D sigma Hs [wD].
    destruct (IHA D sigma Hs (inhabits wD)) as [dA'].
    destruct (IHp (A [sigma] :: D) (up_subst sigma) (sub_ok_up sigma G D A _ wD dA' Hs)
                (inhabits (w_cons D _ _ wD dA'))) as [dp'].
    exact (inhabits (t_all D _ _ j k dA' dp')).
  - (* t_all_intro *) intros G A p t j k dA IHA dp IHp dt IHt D sigma Hs [wD].
    destruct (IHA D sigma Hs (inhabits wD)) as [dA'].
    pose proof (sub_ok_up sigma G D A _ wD dA' Hs) as Hs1.
    pose proof (inhabits (w_cons D (A [sigma]) _ wD dA')) as wD'.
    destruct (IHp (A [sigma] :: D) (up_subst sigma) Hs1 wD') as [dp'].
    destruct (IHt (A [sigma] :: D) (up_subst sigma) Hs1 wD') as [dt'].
    exact (inhabits (t_all_intro D _ _ _ j k dA' dp' dt')).
  - (* t_all_elim *) intros G A p f u j k dA IHA dp IHp df IHf du IHu D sigma Hs [wD].
    destruct (IHA D sigma Hs (inhabits wD)) as [dA'].
    destruct (IHp (A [sigma] :: D) (up_subst sigma) (sub_ok_up sigma G D A _ wD dA' Hs)
                (inhabits (w_cons D _ _ wD dA'))) as [dp'].
    destruct (IHf D sigma Hs (inhabits wD)) as [df'].
    destruct (IHu D sigma Hs (inhabits wD)) as [du'].
    replace ((prf j (p [u..])) [sigma])
      with (prf j ((p [up_subst sigma]) [(u [sigma])..])) by (rasimpl; reflexivity).
    exact (inhabits (t_all_elim D _ _ _ _ j k dA' dp' df' du')).
  - (* t_false *) intros G k W IHW D sigma Hs [wD]; exact (inhabits (t_false D k wD)).
  - (* t_absurd *) intros G T e k j dT IHT de IHe D sigma Hs [wD].
    destruct (IHT D sigma Hs (inhabits wD)) as [dT'].
    destruct (IHe D sigma Hs (inhabits wD)) as [de'].
    exact (inhabits (t_absurd D _ _ k j dT' de')).
  - (* c_refl *) intros G t A d IHd D sigma Hs [wD].
    destruct (IHd D sigma Hs (inhabits wD)) as [d'].
    exact (inhabits (c_refl D _ _ d')).
  - (* c_sym *) intros G t u A c IHc D sigma Hs [wD].
    destruct (IHc D sigma Hs (inhabits wD)) as [c'].
    exact (inhabits (c_sym D _ _ _ c')).
  - (* c_trans *) intros G t u v A c1 IH1 c2 IH2 D sigma Hs [wD].
    destruct (IH1 D sigma Hs (inhabits wD)) as [c1'].
    destruct (IH2 D sigma Hs (inhabits wD)) as [c2'].
    exact (inhabits (c_trans D _ _ _ _ c1' c2')).
  - (* c_conv *) intros G t u A B k c IHc dA IHA dB IHB cAB IHAB D sigma Hs [wD].
    destruct (IHc D sigma Hs (inhabits wD)) as [c'].
    destruct (IHA D sigma Hs (inhabits wD)) as [dA'].
    destruct (IHB D sigma Hs (inhabits wD)) as [dB'].
    destruct (IHAB D sigma Hs (inhabits wD)) as [cAB'].
    exact (inhabits (c_conv D _ _ _ _ k c' dA' dB' cAB')).
  - (* c_prf_irr *) intros G j p e e' dp IHp de IHe de' IHe' D sigma Hs [wD].
    destruct (IHp D sigma Hs (inhabits wD)) as [dp'].
    destruct (IHe D sigma Hs (inhabits wD)) as [de1].
    destruct (IHe' D sigma Hs (inhabits wD)) as [de2].
    exact (inhabits (c_prf_irr D j _ _ _ dp' de1 de2)).
  - (* c_up *) intros G j A A' dA IHA dA' IHA' c IHc D sigma Hs [wD].
    destruct (IHA D sigma Hs (inhabits wD)) as [d1].
    destruct (IHA' D sigma Hs (inhabits wD)) as [d2].
    destruct (IHc D sigma Hs (inhabits wD)) as [c'].
    exact (inhabits (c_up D j _ _ d1 d2 c')).
  - (* c_up_tm *) intros G j A t t' dA IHA dt IHt dt' IHt' c IHc D sigma Hs [wD].
    destruct (IHA D sigma Hs (inhabits wD)) as [d1].
    destruct (IHt D sigma Hs (inhabits wD)) as [d2].
    destruct (IHt' D sigma Hs (inhabits wD)) as [d3].
    destruct (IHc D sigma Hs (inhabits wD)) as [c'].
    exact (inhabits (c_up_tm D j _ _ _ d1 d2 d3 c')).
  - (* c_up_univ *) intros G k j Hjk W IHW D sigma Hs [wD].
    exact (inhabits (c_up_univ D k j Hjk wD)).
  - (* c_up_nat *) intros G k W IHW D sigma Hs [wD].
    exact (inhabits (c_up_nat D k wD)).
  - (* c_up_prop *) intros G k W IHW D sigma Hs [wD].
    exact (inhabits (c_up_prop D k wD)).
  - (* c_up_prf *) intros G k j p Hjk dp IHp D sigma Hs [wD].
    destruct (IHp D sigma Hs (inhabits wD)) as [dp'].
    exact (inhabits (c_up_prf D k j _ Hjk dp')).
  - (* c_up_pi *) intros G k i j A B Hik Hjk dA IHA dB IHB D sigma Hs [wD].
    destruct (IHA D sigma Hs (inhabits wD)) as [dA'].
    destruct (IHB (A [sigma] :: D) (up_subst sigma)
                (sub_ok_up sigma G D A i wD dA' Hs)
                (inhabits (w_cons D _ _ wD dA'))) as [dB'].
    exact (inhabits (c_up_pi D k i j _ _ Hik Hjk dA' dB')).
  - (* c_up_sig *) intros G k i j A B Hik Hjk dA IHA dB IHB D sigma Hs [wD].
    destruct (IHA D sigma Hs (inhabits wD)) as [dA'].
    destruct (IHB (A [sigma] :: D) (up_subst sigma)
                (sub_ok_up sigma G D A i wD dA' Hs)
                (inhabits (w_cons D _ _ wD dA'))) as [dB'].
    exact (inhabits (c_up_sig D k i j _ _ Hik Hjk dA' dB')).
  - (* c_up_w *) intros G k i j A B Hik Hjk dA IHA dB IHB D sigma Hs [wD].
    destruct (IHA D sigma Hs (inhabits wD)) as [dA'].
    destruct (IHB (A [sigma] :: D) (up_subst sigma)
                (sub_ok_up sigma G D A i wD dA' Hs)
                (inhabits (w_cons D _ _ wD dA'))) as [dB'].
    exact (inhabits (c_up_w D k i j _ _ Hik Hjk dA' dB')).
  - (* c_pi *) intros G k i j A A' B B' Hik Hjk dA IHA dB IHB dA' IHA' dB' IHB' cA IHcA cB IHcB
      D sigma Hs [wD].
    destruct (IHA D sigma Hs (inhabits wD)) as [d1].
    destruct (IHA' D sigma Hs (inhabits wD)) as [d3].
    pose proof (sub_ok_up sigma G D A _ wD d1 Hs) as Hs1.
    destruct (IHB (A [sigma] :: D) (up_subst sigma) Hs1
                (inhabits (w_cons D _ _ wD d1))) as [d2].
    destruct (IHB' (A' [sigma] :: D) (up_subst sigma)
                (sub_ok_up sigma G D A' _ wD d3 Hs)
                (inhabits (w_cons D _ _ wD d3))) as [d4].
    destruct (IHcA D sigma Hs (inhabits wD)) as [cA'].
    destruct (IHcB (A [sigma] :: D) (up_subst sigma) Hs1
                (inhabits (w_cons D _ _ wD d1))) as [cB'].
    exact (inhabits (c_pi D k i j _ _ _ _ Hik Hjk d1 d2 d3 d4 cA' cB')).
  - (* c_lam *) intros G k i j A A' B B' t t' Hik Hjk dA IHA dB IHB dA' IHA' dB' IHB'
      cA IHcA cB IHcB dt IHt dt' IHt' ct IHct D sigma Hs [wD].
    destruct (IHA D sigma Hs (inhabits wD)) as [d1].
    destruct (IHA' D sigma Hs (inhabits wD)) as [d3].
    pose proof (sub_ok_up sigma G D A _ wD d1 Hs) as Hs1.
    pose proof (sub_ok_up sigma G D A' _ wD d3 Hs) as Hs2.
    pose proof (inhabits (w_cons D (A [sigma]) _ wD d1)) as wD1.
    pose proof (inhabits (w_cons D (A' [sigma]) _ wD d3)) as wD2.
    destruct (IHB (A [sigma] :: D) (up_subst sigma) Hs1 wD1) as [d2].
    destruct (IHB' (A' [sigma] :: D) (up_subst sigma) Hs2 wD2) as [d4].
    destruct (IHcA D sigma Hs (inhabits wD)) as [cA'].
    destruct (IHcB (A [sigma] :: D) (up_subst sigma) Hs1 wD1) as [cB'].
    destruct (IHt (A [sigma] :: D) (up_subst sigma) Hs1 wD1) as [d5].
    destruct (IHt' (A' [sigma] :: D) (up_subst sigma) Hs2 wD2) as [d6].
    destruct (IHct (A [sigma] :: D) (up_subst sigma) Hs1 wD1) as [ct'].
    exact (inhabits (c_lam D k i j _ _ _ _ _ _ Hik Hjk d1 d2 d3 d4 cA' cB' d5 d6 ct')).
  - (* c_app *) intros G k i j A B f f' u u' Hik Hjk dA IHA dB IHB df IHf df' IHf' cf IHcf
      du IHu du' IHu' cu IHcu D sigma Hs [wD].
    destruct (IHA D sigma Hs (inhabits wD)) as [d1].
    destruct (IHB (A [sigma] :: D) (up_subst sigma) (sub_ok_up sigma G D A _ wD d1 Hs)
                (inhabits (w_cons D _ _ wD d1))) as [d2].
    destruct (IHf D sigma Hs (inhabits wD)) as [d3].
    destruct (IHf' D sigma Hs (inhabits wD)) as [d4].
    destruct (IHcf D sigma Hs (inhabits wD)) as [cf'].
    destruct (IHu D sigma Hs (inhabits wD)) as [d5].
    destruct (IHu' D sigma Hs (inhabits wD)) as [d6].
    destruct (IHcu D sigma Hs (inhabits wD)) as [cu'].
    replace ((B [u..]) [sigma]) with ((B [up_subst sigma]) [(u [sigma])..])
      by (rasimpl; reflexivity).
    exact (inhabits (c_app D k i j _ _ _ _ _ _ Hik Hjk d1 d2 d3 d4 cf' d5 d6 cu')).
  - (* c_beta *) intros G k i j A B t u Hik Hjk dA IHA dB IHB dt IHt du IHu D sigma Hs [wD].
    destruct (IHA D sigma Hs (inhabits wD)) as [d1].
    pose proof (sub_ok_up sigma G D A _ wD d1 Hs) as Hs1.
    pose proof (inhabits (w_cons D (A [sigma]) _ wD d1)) as wD'.
    destruct (IHB (A [sigma] :: D) (up_subst sigma) Hs1 wD') as [d2].
    destruct (IHt (A [sigma] :: D) (up_subst sigma) Hs1 wD') as [d3].
    destruct (IHu D sigma Hs (inhabits wD)) as [d4].
    replace ((B [u..]) [sigma]) with ((B [up_subst sigma]) [(u [sigma])..])
      by (rasimpl; reflexivity).
    replace ((t [u..]) [sigma]) with ((t [up_subst sigma]) [(u [sigma])..])
      by (rasimpl; reflexivity).
    exact (inhabits (c_beta D k i j _ _ _ _ Hik Hjk d1 d2 d3 d4)).
  - (* c_eta *) intros G k i j A B f Hik Hjk dA IHA dB IHB df IHf D sigma Hs [wD].
    destruct (IHA D sigma Hs (inhabits wD)) as [d1].
    destruct (IHB (A [sigma] :: D) (up_subst sigma) (sub_ok_up sigma G D A _ wD d1 Hs)
                (inhabits (w_cons D _ _ wD d1))) as [d2].
    destruct (IHf D sigma Hs (inhabits wD)) as [d3].
    rewrite eta_subst.
    exact (inhabits (c_eta D k i j _ _ _ Hik Hjk d1 d2 d3)).
  - (* c_sig *) intros G k i j A A' B B' Hik Hjk dA IHA dB IHB dA' IHA' dB' IHB' cA IHcA cB IHcB
      D sigma Hs [wD].
    destruct (IHA D sigma Hs (inhabits wD)) as [d1].
    destruct (IHA' D sigma Hs (inhabits wD)) as [d3].
    pose proof (sub_ok_up sigma G D A _ wD d1 Hs) as Hs1.
    destruct (IHB (A [sigma] :: D) (up_subst sigma) Hs1
                (inhabits (w_cons D _ _ wD d1))) as [d2].
    destruct (IHB' (A' [sigma] :: D) (up_subst sigma)
                (sub_ok_up sigma G D A' _ wD d3 Hs)
                (inhabits (w_cons D _ _ wD d3))) as [d4].
    destruct (IHcA D sigma Hs (inhabits wD)) as [cA'].
    destruct (IHcB (A [sigma] :: D) (up_subst sigma) Hs1
                (inhabits (w_cons D _ _ wD d1))) as [cB'].
    exact (inhabits (c_sig D k i j _ _ _ _ Hik Hjk d1 d2 d3 d4 cA' cB')).
  - (* c_pair *) intros G k i j A B t t' u u' Hik Hjk dA IHA dB IHB dt IHt dt' IHt' ct IHct
      du IHu du' IHu' cu IHcu D sigma Hs [wD].
    destruct (IHA D sigma Hs (inhabits wD)) as [d1].
    destruct (IHB (A [sigma] :: D) (up_subst sigma) (sub_ok_up sigma G D A _ wD d1 Hs)
                (inhabits (w_cons D _ _ wD d1))) as [d2].
    destruct (IHt D sigma Hs (inhabits wD)) as [d3].
    destruct (IHt' D sigma Hs (inhabits wD)) as [d4].
    destruct (IHct D sigma Hs (inhabits wD)) as [ct'].
    destruct (IHu D sigma Hs (inhabits wD)) as [d5].
    destruct (IHu' D sigma Hs (inhabits wD)) as [d6].
    destruct (IHcu D sigma Hs (inhabits wD)) as [cu'].
    replace ((B [t..]) [sigma]) with ((B [up_subst sigma]) [(t [sigma])..])
      in d5, d6, cu' by (rasimpl; reflexivity).
    exact (inhabits (c_pair D k i j _ _ _ _ _ _ Hik Hjk d1 d2 d3 d4 ct' d5 d6 cu')).
  - (* c_fst *) intros G k i j A B p p' Hik Hjk dA IHA dB IHB dp IHp dp' IHp' cp IHcp
      D sigma Hs [wD].
    destruct (IHA D sigma Hs (inhabits wD)) as [d1].
    destruct (IHB (A [sigma] :: D) (up_subst sigma) (sub_ok_up sigma G D A _ wD d1 Hs)
                (inhabits (w_cons D _ _ wD d1))) as [d2].
    destruct (IHp D sigma Hs (inhabits wD)) as [d3].
    destruct (IHp' D sigma Hs (inhabits wD)) as [d4].
    destruct (IHcp D sigma Hs (inhabits wD)) as [cp'].
    exact (inhabits (c_fst D k i j _ _ _ _ Hik Hjk d1 d2 d3 d4 cp')).
  - (* c_snd *) intros G k i j A B p p' Hik Hjk dA IHA dB IHB dp IHp dp' IHp' cp IHcp
      D sigma Hs [wD].
    destruct (IHA D sigma Hs (inhabits wD)) as [d1].
    destruct (IHB (A [sigma] :: D) (up_subst sigma) (sub_ok_up sigma G D A _ wD d1 Hs)
                (inhabits (w_cons D _ _ wD d1))) as [d2].
    destruct (IHp D sigma Hs (inhabits wD)) as [d3].
    destruct (IHp' D sigma Hs (inhabits wD)) as [d4].
    destruct (IHcp D sigma Hs (inhabits wD)) as [cp'].
    replace ((B [(fst A B p)..]) [sigma])
      with ((B [up_subst sigma])
              [(fst (A [sigma]) (B [up_subst sigma]) (p [sigma]))..])
      by (rasimpl; reflexivity).
    exact (inhabits (c_snd D k i j _ _ _ _ Hik Hjk d1 d2 d3 d4 cp')).
  - (* c_fst_beta *) intros G k i j A B t u Hik Hjk dA IHA dB IHB dt IHt du IHu D sigma Hs [wD].
    destruct (IHA D sigma Hs (inhabits wD)) as [d1].
    destruct (IHB (A [sigma] :: D) (up_subst sigma) (sub_ok_up sigma G D A _ wD d1 Hs)
                (inhabits (w_cons D _ _ wD d1))) as [d2].
    destruct (IHt D sigma Hs (inhabits wD)) as [d3].
    destruct (IHu D sigma Hs (inhabits wD)) as [d4].
    replace ((B [t..]) [sigma]) with ((B [up_subst sigma]) [(t [sigma])..]) in d4
      by (rasimpl; reflexivity).
    exact (inhabits (c_fst_beta D k i j _ _ _ _ Hik Hjk d1 d2 d3 d4)).
  - (* c_snd_beta *) intros G k i j A B t u Hik Hjk dA IHA dB IHB dt IHt du IHu D sigma Hs [wD].
    destruct (IHA D sigma Hs (inhabits wD)) as [d1].
    destruct (IHB (A [sigma] :: D) (up_subst sigma) (sub_ok_up sigma G D A _ wD d1 Hs)
                (inhabits (w_cons D _ _ wD d1))) as [d2].
    destruct (IHt D sigma Hs (inhabits wD)) as [d3].
    destruct (IHu D sigma Hs (inhabits wD)) as [d4].
    replace ((B [t..]) [sigma]) with ((B [up_subst sigma]) [(t [sigma])..])
      in d4 |- * by (rasimpl; reflexivity).
    exact (inhabits (c_snd_beta D k i j _ _ _ _ Hik Hjk d1 d2 d3 d4)).
  - (* c_surj *) intros G k i j A B p Hik Hjk dA IHA dB IHB dp IHp D sigma Hs [wD].
    destruct (IHA D sigma Hs (inhabits wD)) as [d1].
    destruct (IHB (A [sigma] :: D) (up_subst sigma) (sub_ok_up sigma G D A _ wD d1 Hs)
                (inhabits (w_cons D _ _ wD d1))) as [d2].
    destruct (IHp D sigma Hs (inhabits wD)) as [d3].
    exact (inhabits (c_surj D k i j _ _ _ Hik Hjk d1 d2 d3)).
  - (* c_w *) intros G k i j A A' B B' Hik Hjk dA IHA dB IHB dA' IHA' dB' IHB'
      cA IHcA cB IHcB D sigma Hs [wD].
    destruct (IHA D sigma Hs (inhabits wD)) as [d1].
    destruct (IHA' D sigma Hs (inhabits wD)) as [d3].
    pose proof (sub_ok_up sigma G D A i wD d1 Hs) as Hs1.
    pose proof (sub_ok_up sigma G D A' i wD d3 Hs) as Hs2.
    destruct (IHB (A [sigma] :: D) (up_subst sigma) Hs1
                (inhabits (w_cons D _ _ wD d1))) as [d2].
    destruct (IHB' (A' [sigma] :: D) (up_subst sigma) Hs2
                (inhabits (w_cons D _ _ wD d3))) as [d4].
    destruct (IHcA D sigma Hs (inhabits wD)) as [cA'].
    destruct (IHcB (A [sigma] :: D) (up_subst sigma) Hs1
                (inhabits (w_cons D _ _ wD d1))) as [cB'].
    exact (inhabits (c_w D k i j _ _ _ _ Hik Hjk d1 d2 d3 d4 cA' cB')).
  - (* c_sup *) intros G k i j A B a a' f f' Hik Hjk dA IHA dB IHB
      da IHa da' IHa' ca IHca df IHf df' IHf' cf IHcf D sigma Hs [wD].
    destruct (IHA D sigma Hs (inhabits wD)) as [dA'].
    destruct (IHB (A [sigma] :: D) (up_subst sigma)
                (sub_ok_up sigma G D A i wD dA' Hs)
                (inhabits (w_cons D _ _ wD dA'))) as [dB'].
    destruct (IHa D sigma Hs (inhabits wD)) as [d1].
    destruct (IHa' D sigma Hs (inhabits wD)) as [d2].
    destruct (IHca D sigma Hs (inhabits wD)) as [c1].
    destruct (IHf D sigma Hs (inhabits wD)) as [d3].
    destruct (IHf' D sigma Hs (inhabits wD)) as [d4].
    destruct (IHcf D sigma Hs (inhabits wD)) as [c2].
    rewrite sup_fun_subst in d3, d4, c2.
    exact (inhabits (c_sup D k i j _ _ _ _ _ _ Hik Hjk dA' dB'
                      d1 d2 c1 d3 d4 c2)).
  - (* c_wrec *) intros G k i j m n A B C C' s s' w w' Hik Hjk Hjn Hmn En
      dA IHA dB IHB dC IHC dC' IHC' cC IHcC dbr IHbr dih IHih
      ds IHs ds' IHs' cs IHcs dw IHw dw' IHw' cw IHcw D sigma Hs [wD].
    destruct (IHA D sigma Hs (inhabits wD)) as [dA1].
    pose proof (sub_ok_up sigma G D A i wD dA1 Hs) as Hup1.
    pose proof (w_cons D (A [sigma]) _ wD dA1) as wD1.
    destruct (IHB (A [sigma] :: D) (up_subst sigma) Hup1 (inhabits wD1)) as [dB1].
    pose proof (t_w D k i j _ _ Hik Hjk dA1 dB1) as dW1.
    pose proof (sub_ok_up sigma G D (wt k A B) k wD dW1 Hs) as HupW.
    pose proof (inhabits (w_cons D _ _ wD dW1)) as wDW.
    destruct (IHC ((wt k A B) [sigma] :: D) (up_subst sigma) HupW wDW) as [dC1].
    destruct (IHC' ((wt k A B) [sigma] :: D) (up_subst sigma) HupW wDW) as [dC2].
    destruct (IHcC ((wt k A B) [sigma] :: D) (up_subst sigma) HupW wDW) as [cC1].
    destruct (IHbr (A [sigma] :: D) (up_subst sigma) Hup1 (inhabits wD1)) as [dbr1].
    rewrite wbr_subst in dbr1.
    pose proof (w_cons _ _ _ wD1 dbr1) as wD2.
    pose proof (sub_ok_wstep sigma G D k n i A B C wD dA1 dbr1) as Hup3.
    pose proof (sub_ok_up (up_subst sigma) (A :: G) (A [sigma] :: D)
                  (wbr k A B) k wD1
                  (eq_rect _ (fun X => ty (A [sigma] :: D) X (UU k)) dbr1 _
                     (eq_sym (wbr_subst k A B sigma))) Hup1) as Hup2.
    rewrite wbr_subst in Hup2.
    destruct (IHih _ (up_subst (up_subst sigma)) Hup2 (inhabits wD2)) as [dih1].
    rewrite wih_subst in dih1.
    pose proof (w_cons _ _ _ wD2 dih1) as wD3.
    specialize (Hup3 dih1 Hs).
    destruct (IHs _ (up_subst (up_subst (up_subst sigma))) Hup3
                (inhabits wD3)) as [ds1].
    destruct (IHs' _ (up_subst (up_subst (up_subst sigma))) Hup3
                (inhabits wD3)) as [ds2].
    destruct (IHcs _ (up_subst (up_subst (up_subst sigma))) Hup3
                (inhabits wD3)) as [cs1].
    rewrite wsup_ty_subst in ds1, ds2, cs1.
    destruct (IHw D sigma Hs (inhabits wD)) as [dw1].
    destruct (IHw' D sigma Hs (inhabits wD)) as [dw2].
    destruct (IHcw D sigma Hs (inhabits wD)) as [cw1].
    replace ((C [w..]) [sigma]) with ((C [up_subst sigma]) [(w [sigma])..])
      by (rasimpl; reflexivity).
    exact (inhabits (c_wrec D k i j m n _ _ _ _ _ _ _ _ Hik Hjk Hjn Hmn En
                      dA1 dB1 dC1 dC2 cC1 dbr1 dih1 ds1 ds2 cs1 dw1 dw2 cw1)).
  - (* c_wrec_sup *) intros G k i j m n A B C s a f Hik Hjk Hjn Hmn En
      dA IHA dB IHB dC IHC dbr IHbr dih IHih ds IHs da IHa df IHf
      D sigma Hs [wD].
    destruct (IHA D sigma Hs (inhabits wD)) as [dA1].
    pose proof (sub_ok_up sigma G D A i wD dA1 Hs) as Hup1.
    pose proof (w_cons D (A [sigma]) _ wD dA1) as wD1.
    destruct (IHB (A [sigma] :: D) (up_subst sigma) Hup1 (inhabits wD1)) as [dB1].
    pose proof (t_w D k i j _ _ Hik Hjk dA1 dB1) as dW1.
    destruct (IHC ((wt k A B) [sigma] :: D) (up_subst sigma)
                (sub_ok_up sigma G D (wt k A B) k wD dW1 Hs)
                (inhabits (w_cons D _ _ wD dW1))) as [dC1].
    destruct (IHbr (A [sigma] :: D) (up_subst sigma) Hup1 (inhabits wD1)) as [dbr1].
    rewrite wbr_subst in dbr1.
    pose proof (w_cons _ _ _ wD1 dbr1) as wD2.
    pose proof (sub_ok_wstep sigma G D k n i A B C wD dA1 dbr1) as Hup3.
    pose proof (sub_ok_up (up_subst sigma) (A :: G) (A [sigma] :: D)
                  (wbr k A B) k wD1
                  (eq_rect _ (fun X => ty (A [sigma] :: D) X (UU k)) dbr1 _
                     (eq_sym (wbr_subst k A B sigma))) Hup1) as Hup2.
    rewrite wbr_subst in Hup2.
    destruct (IHih _ (up_subst (up_subst sigma)) Hup2 (inhabits wD2)) as [dih1].
    rewrite wih_subst in dih1.
    pose proof (w_cons _ _ _ wD2 dih1) as wD3.
    specialize (Hup3 dih1 Hs).
    destruct (IHs _ (up_subst (up_subst (up_subst sigma))) Hup3
                (inhabits wD3)) as [ds1].
    rewrite wsup_ty_subst in ds1.
    destruct (IHa D sigma Hs (inhabits wD)) as [da1].
    destruct (IHf D sigma Hs (inhabits wD)) as [df1].
    rewrite sup_fun_subst in df1.
    rewrite wrec_sup_contractum_subst.
    replace ((C [(sup k A B a f)..]) [sigma])
      with ((C [up_subst sigma])
              [(sup k (A [sigma]) (B [up_subst sigma]) (a [sigma]) (f [sigma]))..])
      by (rasimpl; reflexivity).
    exact (inhabits (c_wrec_sup D k i j m n _ _ _ _ _ _ Hik Hjk Hjn Hmn En
                      dA1 dB1 dC1 dbr1 dih1 ds1 da1 df1)).
  - (* c_succ *) intros G k n n' dn IHn dn' IHn' cn IHcn D sigma Hs [wD].
    destruct (IHn D sigma Hs (inhabits wD)) as [d1].
    destruct (IHn' D sigma Hs (inhabits wD)) as [d2].
    destruct (IHcn D sigma Hs (inhabits wD)) as [c'].
    exact (inhabits (c_succ D _ _ _ d1 d2 c')).
  - (* c_natrec *) intros G C C' z z' s s' n n' k j dC IHC dC' IHC' cC IHcC
      dz IHz dz' IHz' cz IHcz ds IHs ds' IHs' cs IHcs dn IHn dn' IHn' cn IHcn
      D sigma Hs [wD].
    pose proof (w_cons D (nat_ j) j wD (t_nat D j wD)) as wDn.
    pose proof (sub_ok_up sigma G D (nat_ j) j wD (t_nat D j wD) Hs) as Hs1.
    destruct (IHC (nat_ j :: D) (up_subst sigma) Hs1 (inhabits wDn)) as [d1].
    destruct (IHC' (nat_ j :: D) (up_subst sigma) Hs1 (inhabits wDn)) as [d2].
    destruct (IHcC (nat_ j :: D) (up_subst sigma) Hs1 (inhabits wDn)) as [cC'].
    destruct (IHz D sigma Hs (inhabits wD)) as [d3].
    destruct (IHz' D sigma Hs (inhabits wD)) as [d4].
    destruct (IHcz D sigma Hs (inhabits wD)) as [cz'].
    pose proof (sub_ok_up (up_subst sigma) (nat_ j :: G) (nat_ j :: D) C _ wDn d1 Hs1)
      as Hs2.
    pose proof (inhabits (w_cons (nat_ j :: D) (C [up_subst sigma]) _ wDn d1)) as wDc.
    destruct (IHs (C [up_subst sigma] :: nat_ j :: D) (up_subst (up_subst sigma))
                Hs2 wDc) as [d5].
    destruct (IHs' (C [up_subst sigma] :: nat_ j :: D) (up_subst (up_subst sigma))
                Hs2 wDc) as [d6].
    destruct (IHcs (C [up_subst sigma] :: nat_ j :: D) (up_subst (up_subst sigma))
                Hs2 wDc) as [cs'].
    destruct (IHn D sigma Hs (inhabits wD)) as [d7].
    destruct (IHn' D sigma Hs (inhabits wD)) as [d8].
    destruct (IHcn D sigma Hs (inhabits wD)) as [cn'].
    replace ((C [(zero j)..]) [sigma]) with ((C [up_subst sigma]) [(zero j)..])
      in d3, d4, cz' by (rasimpl; reflexivity).
    rewrite nrec_succ_subst in d5, d6, cs'.
    replace ((C [n..]) [sigma]) with ((C [up_subst sigma]) [(n [sigma])..])
      by (rasimpl; reflexivity).
    exact (inhabits (c_natrec D _ _ _ _ _ _ _ _ k j d1 d2 cC' d3 d4 cz'
                       d5 d6 cs' d7 d8 cn')).
  - (* c_rec_zero *) intros G C z s k j dC IHC dz IHz ds IHs D sigma Hs [wD].
    pose proof (w_cons D (nat_ j) j wD (t_nat D j wD)) as wDn.
    pose proof (sub_ok_up sigma G D (nat_ j) j wD (t_nat D j wD) Hs) as Hs1.
    destruct (IHC (nat_ j :: D) (up_subst sigma) Hs1 (inhabits wDn)) as [d1].
    destruct (IHz D sigma Hs (inhabits wD)) as [d2].
    destruct (IHs (C [up_subst sigma] :: nat_ j :: D) (up_subst (up_subst sigma))
                (sub_ok_up (up_subst sigma) (nat_ j :: G) (nat_ j :: D) C _ wDn d1 Hs1)
                (inhabits (w_cons (nat_ j :: D) _ _ wDn d1))) as [d3].
    rewrite nrec_succ_subst in d3.
    replace ((C [(zero j)..]) [sigma]) with ((C [up_subst sigma]) [(zero j)..])
      in d2 |- * by (rasimpl; reflexivity).
    exact (inhabits (c_rec_zero D _ _ _ k j d1 d2 d3)).
  - (* c_rec_succ *) intros G C z s n k j dC IHC dz IHz ds IHs dn IHn D sigma Hs [wD].
    pose proof (w_cons D (nat_ j) j wD (t_nat D j wD)) as wDn.
    pose proof (sub_ok_up sigma G D (nat_ j) j wD (t_nat D j wD) Hs) as Hs1.
    destruct (IHC (nat_ j :: D) (up_subst sigma) Hs1 (inhabits wDn)) as [d1].
    destruct (IHz D sigma Hs (inhabits wD)) as [d2].
    destruct (IHs (C [up_subst sigma] :: nat_ j :: D) (up_subst (up_subst sigma))
                (sub_ok_up (up_subst sigma) (nat_ j :: G) (nat_ j :: D) C _ wDn d1 Hs1)
                (inhabits (w_cons (nat_ j :: D) _ _ wDn d1))) as [d3].
    destruct (IHn D sigma Hs (inhabits wD)) as [d4].
    rewrite nrec_succ_subst in d3.
    replace ((C [(zero j)..]) [sigma]) with ((C [up_subst sigma]) [(zero j)..]) in d2
      by (rasimpl; reflexivity).
    rewrite rec_succ_subst.
    replace ((C [(succ n)..]) [sigma])
      with ((C [up_subst sigma]) [(succ (n [sigma]))..]) by (rasimpl; reflexivity).
    exact (inhabits (c_rec_succ D _ _ _ _ k j d1 d2 d3 d4)).
  - (* c_prf *) intros G k j p p' Hjk dp IHp dp' IHp' c IHc D sigma Hs [wD].
    destruct (IHp D sigma Hs (inhabits wD)) as [d1].
    destruct (IHp' D sigma Hs (inhabits wD)) as [d2].
    destruct (IHc D sigma Hs (inhabits wD)) as [c'].
    exact (inhabits (c_prf D k j _ _ Hjk d1 d2 c')).
  - (* c_all *) intros G A A' p p' j k dA IHA dp IHp dA' IHA' dp' IHp' cA IHcA cp IHcp
      D sigma Hs [wD].
    destruct (IHA D sigma Hs (inhabits wD)) as [d1].
    destruct (IHA' D sigma Hs (inhabits wD)) as [d3].
    pose proof (sub_ok_up sigma G D A _ wD d1 Hs) as Hs1.
    destruct (IHp (A [sigma] :: D) (up_subst sigma) Hs1
                (inhabits (w_cons D _ _ wD d1))) as [d2].
    destruct (IHp' (A' [sigma] :: D) (up_subst sigma)
                (sub_ok_up sigma G D A' _ wD d3 Hs)
                (inhabits (w_cons D _ _ wD d3))) as [d4].
    destruct (IHcA D sigma Hs (inhabits wD)) as [cA'].
    destruct (IHcp (A [sigma] :: D) (up_subst sigma) Hs1
                (inhabits (w_cons D _ _ wD d1))) as [cp'].
    exact (inhabits (c_all D _ _ _ _ j k d1 d2 d3 d4 cA' cp')).
Qed.

(* ---- the two corollaries the fundamental lemma consumes ---- *)

(* Context validity: every judgement presupposes a well-formed context.  Each
   rule has at least one premise in its own context, so every case is the
   corresponding induction hypothesis. *)
Theorem ctx_valid :
  (forall G, wfc G -> inhabited (wfc G))
  /\ (forall G t A, ty G t A -> inhabited (wfc G))
  /\ (forall G t u A, cv G t u A -> inhabited (wfc G)).
Proof.
  apply wty_min;
    [ exact (inhabits w_nil)
    | intros G A k W IHW dA IHA; exact (inhabits (w_cons G A k W dA))
    | .. ];
    intros; assumption.
Qed.

Corollary ty_wfc G t A : ty G t A -> inhabited (wfc G).
Proof. exact (proj1 (proj2 ctx_valid) G t A). Qed.

Corollary ty_subst G t A (d : ty G t A) D sigma :
  sub_ok sigma G D -> inhabited (wfc D) -> inhabited (ty D (t [sigma]) (A [sigma])).
Proof. exact (proj1 (proj2 substitution) G t A d D sigma). Qed.

Corollary cv_subst G t u A (c : cv G t u A) D sigma :
  sub_ok sigma G D -> inhabited (wfc D) ->
  inhabited (cv D (t [sigma]) (u [sigma]) (A [sigma])).
Proof. exact (proj2 (proj2 substitution) G t u A c D sigma). Qed.

Lemma sub_ok_one G A u (wG : wfc G) (du : ty G u A) : sub_ok (u..) (A :: G) G.
Proof.
  intros i T Hl; inversion Hl; subst.
  - replace ((A ⟨↑⟩) [u..]) with A by (rasimpl; reflexivity).
    exact (inhabits du).
  - match goal with
    | H0 : lookup ?i0 G ?T0 |- _ =>
        replace ((T0 ⟨↑⟩) [u..]) with T0 by (rasimpl; reflexivity);
        exact (inhabits (t_var G i0 T0 wG H0))
    end.
Qed.

(* The form the layer-2 fundamental lemma uses: the type of a rule whose
   conclusion is a substitution instance is itself well typed. *)
Corollary ty_subst1 G A B C u (dB : ty (A :: G) B C) (du : ty G u A) :
  inhabited (ty G (B [u..]) (C [u..])).
Proof.
  destruct (ty_wfc G u A du) as [wG].
  exact (ty_subst (A :: G) B C dB G (u..) (sub_ok_one G A u wG du) (inhabits wG)).
Qed.

(* ---- the recursor's step rule: the two-place substitution it performs,
     and the typing of the right-hand side it produces ---- *)

(* The step rule's right-hand side is a two-place substitution instance, so
   its typing needs the substitution it performs to be well typed. *)
Lemma sub_ok_rec_succ G C z s n k j (W : wfc G)
  (dC : ty (nat_ j :: G) C (UU k)) (dz : ty G z (C [(zero j)..]))
  (ds : ty (C :: nat_ j :: G) s (nrec_succ C)) (dn : ty G n (nat_ j)) :
  sub_ok ((natrec C z s n) .: n ..) (C :: nat_ j :: G) G.
Proof.
  intros i A Hl; inversion Hl; subst.
  - replace ((C ⟨↑⟩) [(natrec C z s n) .: n ..]) with (C [n..])
      by (rasimpl; reflexivity).
    exact (inhabits (t_natrec G C z s n k j dC dz ds dn)).
  - match goal with
    | H : lookup ?i0 (nat_ j :: G) ?A0 |- _ => inversion H; subst
    end.
    + replace ((((nat_ j) ⟨↑⟩) ⟨↑⟩) [(natrec C z s n) .: n ..]) with (nat_ j)
        by (rasimpl; reflexivity).
      exact (inhabits dn).
    + match goal with
      | H : lookup ?i1 G ?A1 |- _ =>
          replace (((A1 ⟨↑⟩) ⟨↑⟩) [(natrec C z s n) .: n ..]) with A1
            by (rasimpl; reflexivity);
          exact (inhabits (t_var G i1 A1 W H))
      end.
Qed.

Lemma ty_rec_succ_rhs G C z s n k j (W : wfc G)
  (dC : ty (nat_ j :: G) C (UU k)) (dz : ty G z (C [(zero j)..]))
  (ds : ty (C :: nat_ j :: G) s (nrec_succ C)) (dn : ty G n (nat_ j)) :
  inhabited (ty G (s [(natrec C z s n) .: n ..]) (C [(succ n)..])).
Proof.
  destruct (ty_subst (C :: nat_ j :: G) s (nrec_succ C) ds G
              ((natrec C z s n) .: n ..)
              (sub_ok_rec_succ G C z s n k j W dC dz ds dn) (inhabits W)) as [d].
  replace ((nrec_succ C) [(natrec C z s n) .: n ..]) with (C [(succ n)..]) in d
    by (unfold nrec_succ; rasimpl; reflexivity).
  exact (inhabits d).
Qed.

(* The step rule fills the step's TWO variables with one substitution.  The
   fundamental lemma gets there by two single substitutions, which is this
   identity (`upn 1 (n..)` is `up_subst (n..)` and `upn 0` is the identity). *)
Lemma rec_succ_two (s n r : tm) : (s [up_subst (n..)]) [r..] = s [r .: n ..].
Proof. rasimpl; reflexivity. Qed.

(* ---- the computation rule's right-hand side.  The step is fed the label,
     the branching function and the induction hypothesis `wih_val`, whose own
     typing is the general form of Typing/Rules.v's closed `ty_wih_val`
     test. ---- *)

Lemma wsub_sub (k : nat) (A B a f u : tm) :
  ((wt k A B) ⟨↑⟩ ⟨↑⟩) [u..] = (wt k A B) ⟨↑⟩.
Proof. rasimpl; reflexivity. Qed.

Lemma wsup_fun_ren (k : nat) (A B a : tm) :
  (pi k (B [a..]) ((wt k A B) ⟨↑⟩)) ⟨↑⟩
  = pi k ((B [a..]) ⟨↑⟩) ((wt k A B) ⟨↑⟩ ⟨↑⟩).
Proof. rasimpl; reflexivity. Qed.

Lemma ty_wsub G k i j A B a f (W : wfc G) (Hik : i <= k) (Hjk : j <= k)
  (dAt : ty G A (UU i)) (dBt : ty (A :: G) B (UU j))
  (da : ty G a A) (df : ty G f (pi k (B [a..]) ((wt k A B) ⟨↑⟩))) :
  inhabited (ty ((B [a..]) :: G) (wsub k A B a f) ((wt k A B) ⟨↑⟩)).
Proof.
  destruct (ty_subst1 G A B (UU j) a dBt da) as [dBa].
  pose proof (w_cons G (B [a..]) j W dBa) as WB.
  destruct (ty_ren G (B [a..]) (UU j) dBa ((B [a..]) :: G) ↑
              (ren_ok_shift G (B [a..])) (inhabits WB)) as [dBa1].
  destruct (ty_ren G (wt k A B) (UU k) (t_w G k i j A B Hik Hjk dAt dBt)
              ((B [a..]) :: G) ↑ (ren_ok_shift G (B [a..]))
              (inhabits WB)) as [dW1].
  destruct (ty_ren ((B [a..]) :: G) ((wt k A B) ⟨↑⟩) (UU k) dW1
              (((B [a..]) ⟨↑⟩) :: (B [a..]) :: G) ↑
              (ren_ok_shift ((B [a..]) :: G) ((B [a..]) ⟨↑⟩))
              (inhabits (w_cons ((B [a..]) :: G) ((B [a..]) ⟨↑⟩) j WB dBa1)))
    as [dW2].
  destruct (ty_ren G f (pi k (B [a..]) ((wt k A B) ⟨↑⟩)) df
              ((B [a..]) :: G) ↑ (ren_ok_shift G (B [a..])) (inhabits WB))
    as [df1].
  rewrite wsup_fun_ren in df1.
  pose proof (t_app ((B [a..]) :: G) k j k ((B [a..]) ⟨↑⟩)
                ((wt k A B) ⟨↑⟩ ⟨↑⟩) (f ⟨↑⟩) (var_tm 0) Hjk (le_n k)
                dBa1 dW2 df1
                (t_var ((B [a..]) :: G) 0 ((B [a..]) ⟨↑⟩) WB
                   (lookup_O G (B [a..])))) as dap.
  rewrite (wsub_sub k A B a f (var_tm 0)) in dap.
  exact (inhabits dap).
Qed.

Lemma wih_val_cod (C w : tm) : (C ⟨up_ren ↑⟩) [w..] = C [ w .:s ↑ ].
Proof. rasimpl; reflexivity. Qed.

Lemma ty_wih_val_gen G k i j m n A B C s a f (W : wfc G)
  (Hik : i <= k) (Hjk : j <= k) (Hjn : j <= n) (Hmn : m <= n)
  (En : n = Nat.max j m)
  (dAt : ty G A (UU i)) (dBt : ty (A :: G) B (UU j))
  (dCt : ty (wt k A B :: G) C (UU m))
  (dbr : ty (A :: G) (wbr k A B) (UU k))
  (dih : ty (wbr k A B :: A :: G) (wih n k A B C) (UU n))
  (ds : ty (wih n k A B C :: wbr k A B :: A :: G) s (wsup_ty k A B C))
  (da : ty G a A) (df : ty G f (pi k (B [a..]) ((wt k A B) ⟨↑⟩))) :
  inhabited (ty G (wih_val n k A B C s a f)
               (pi n (B [a..]) (C [ wsub k A B a f .:s ↑ ]))).
Proof.
  destruct (ty_subst1 G A B (UU j) a dBt da) as [dBa].
  pose proof (w_cons G (B [a..]) j W dBa) as WB.
  (* everything renamed into the context the lambda's body lives in *)
  destruct (ty_ren G A (UU i) dAt ((B [a..]) :: G) ↑
              (ren_ok_shift G (B [a..])) (inhabits WB)) as [dA1].
  pose proof (w_cons ((B [a..]) :: G) (A ⟨↑⟩) i WB dA1) as WA1.
  destruct (ty_ren (A :: G) B (UU j) dBt ((A ⟨↑⟩) :: (B [a..]) :: G)
              (up_ren ↑)
              (ren_ok_up ↑ G ((B [a..]) :: G) A (ren_ok_shift G (B [a..])))
              (inhabits WA1)) as [dB1].
  destruct (ty_ren G (wt k A B) (UU k) (t_w G k i j A B Hik Hjk dAt dBt)
              ((B [a..]) :: G) ↑ (ren_ok_shift G (B [a..])) (inhabits WB))
    as [dW1].
  pose proof (w_cons ((B [a..]) :: G) ((wt k A B) ⟨↑⟩) k WB dW1) as WW1.
  destruct (ty_ren (wt k A B :: G) C (UU m) dCt
              (((wt k A B) ⟨↑⟩) :: (B [a..]) :: G) (up_ren ↑)
              (ren_ok_up ↑ G ((B [a..]) :: G) (wt k A B)
                 (ren_ok_shift G (B [a..]))) (inhabits WW1)) as [dC1].
  destruct (ty_ren (A :: G) (wbr k A B) (UU k) dbr
              ((A ⟨↑⟩) :: (B [a..]) :: G) (up_ren ↑)
              (ren_ok_up ↑ G ((B [a..]) :: G) A (ren_ok_shift G (B [a..])))
              (inhabits WA1)) as [dbr1].
  rewrite wbr_ren in dbr1.
  pose proof (w_cons ((A ⟨↑⟩) :: (B [a..]) :: G)
                (wbr k (A ⟨↑⟩) (B ⟨up_ren ↑⟩)) k WA1 dbr1) as WBR1.
  pose proof (ren_ok_up (up_ren ↑) (A :: G) ((A ⟨↑⟩) :: (B [a..]) :: G)
                (wbr k A B)
                (ren_ok_up ↑ G ((B [a..]) :: G) A
                   (ren_ok_shift G (B [a..])))) as Rok2.
  rewrite wbr_ren in Rok2.
  destruct (ty_ren (wbr k A B :: A :: G) (wih n k A B C) (UU n) dih
              ((wbr k (A ⟨↑⟩) (B ⟨up_ren ↑⟩)) :: (A ⟨↑⟩) :: (B [a..]) :: G)
              (up_ren (up_ren ↑)) Rok2 (inhabits WBR1)) as [dih1].
  rewrite wih_ren in dih1.
  destruct (ty_ren (wih n k A B C :: wbr k A B :: A :: G) s
              (wsup_ty k A B C) ds
              ((wih n k (A ⟨↑⟩) (B ⟨up_ren ↑⟩) (C ⟨up_ren ↑⟩))
                 :: (wbr k (A ⟨↑⟩) (B ⟨up_ren ↑⟩)) :: (A ⟨↑⟩) :: (B [a..]) :: G)
              (up_ren (up_ren (up_ren ↑)))
              (ren_ok_wstep ↑ G ((B [a..]) :: G) k n A B C
                 (ren_ok_shift G (B [a..])))
              (inhabits (w_cons _ _ n WBR1 dih1))) as [ds1].
  rewrite wsup_ty_ren in ds1.
  (* the subtree, and the body *)
  destruct (ty_wsub G k i j A B a f W Hik Hjk dAt dBt da df) as [dsub].
  pose proof (t_wrec ((B [a..]) :: G) k i j m n (A ⟨↑⟩) (B ⟨up_ren ↑⟩)
                (C ⟨up_ren ↑⟩) (s ⟨up_ren (up_ren (up_ren ↑))⟩)
                (wsub k A B a f) Hik Hjk Hjn Hmn En dA1 dB1 dC1 dbr1 dih1 ds1
                dsub) as dbody.
  rewrite wih_val_cod in dbody.
  destruct (ty_subst1 ((B [a..]) :: G) ((wt k A B) ⟨↑⟩) (C ⟨up_ren ↑⟩) (UU m)
              (wsub k A B a f) dC1 dsub) as [dcod].
  rewrite wih_val_cod in dcod.
  exact (inhabits
           (t_lam G n j m (B [a..]) (C [ wsub k A B a f .:s ↑ ])
              (wrec (A ⟨↑⟩) (B ⟨up_ren ↑⟩) (C ⟨up_ren ↑⟩)
                 (s ⟨up_ren (up_ren (up_ren ↑))⟩) (wsub k A B a f))
              Hjn Hmn dBa dcod dbody)).
Qed.

(* the three-place substitution the computation rule performs, and the one
   the fundamental lemma reaches it by: three single substitutions *)
Lemma wrec_sup_three (s a f w : tm) :
  ((s [up_subst (up_subst (a..))]) [up_subst (f..)]) [w..]
  = s [ w .: (f .: a ..) ].
Proof. rasimpl; reflexivity. Qed.

Lemma sub_ok_wsup G k i j m n A B C s a f (W : wfc G)
  (Hik : i <= k) (Hjk : j <= k) (Hjn : j <= n) (Hmn : m <= n)
  (En : n = Nat.max j m)
  (dAt : ty G A (UU i)) (dBt : ty (A :: G) B (UU j))
  (dCt : ty (wt k A B :: G) C (UU m))
  (dbr : ty (A :: G) (wbr k A B) (UU k))
  (dih : ty (wbr k A B :: A :: G) (wih n k A B C) (UU n))
  (ds : ty (wih n k A B C :: wbr k A B :: A :: G) s (wsup_ty k A B C))
  (da : ty G a A) (df : ty G f (pi k (B [a..]) ((wt k A B) ⟨↑⟩))) :
  sub_ok (wih_val n k A B C s a f .: (f .: a ..))
    (wih n k A B C :: wbr k A B :: A :: G) G.
Proof.
  intros idx T Hl.
  revert En; inversion Hl; subst; intros En.
  - replace (((wih n k A B C) ⟨↑⟩) [wih_val n k A B C s a f .: (f .: a ..)])
       with (pi n (B [a..]) (C [ wsub k A B a f .:s ↑ ]))
       by (unfold wih, wsub, sh3; rasimpl; reflexivity).
    exact (ty_wih_val_gen G k i j m n A B C s a f W Hik Hjk Hjn Hmn En
             dAt dBt dCt dbr dih ds da df).
  - clear En.
    match goal with
    | H : lookup ?i0 (wbr k A B :: A :: G) ?T0 |- _ => inversion H; subst
    end.
    + replace (((wbr k A B) ⟨↑⟩ ⟨↑⟩)
                 [wih_val n k A B C s a f .: (f .: a ..)])
         with (pi k (B [a..]) ((wt k A B) ⟨↑⟩))
         by (unfold wbr; rasimpl; reflexivity).
      exact (inhabits df).
    + match goal with
      | H : lookup ?i1 (A :: G) ?T1 |- _ => inversion H; subst
      end.
      * replace (((A ⟨↑⟩) ⟨↑⟩ ⟨↑⟩) [wih_val n k A B C s a f .: (f .: a ..)])
           with A by (rasimpl; reflexivity).
        exact (inhabits da).
      * match goal with
        | H : lookup ?i2 G ?T2 |- _ =>
            replace ((((T2 ⟨↑⟩) ⟨↑⟩) ⟨↑⟩)
                       [wih_val n k A B C s a f .: (f .: a ..)])
              with T2 by (rasimpl; reflexivity);
            exact (inhabits (t_var G i2 T2 W H))
        end.
Qed.

Lemma ty_wrec_sup_rhs G k i j m n A B C s a f (W : wfc G)
  (Hik : i <= k) (Hjk : j <= k) (Hjn : j <= n) (Hmn : m <= n)
  (En : n = Nat.max j m)
  (dAt : ty G A (UU i)) (dBt : ty (A :: G) B (UU j))
  (dCt : ty (wt k A B :: G) C (UU m))
  (dbr : ty (A :: G) (wbr k A B) (UU k))
  (dih : ty (wbr k A B :: A :: G) (wih n k A B C) (UU n))
  (ds : ty (wih n k A B C :: wbr k A B :: A :: G) s (wsup_ty k A B C))
  (da : ty G a A) (df : ty G f (pi k (B [a..]) ((wt k A B) ⟨↑⟩))) :
  inhabited (ty G (s [ wih_val n k A B C s a f .: (f .: a ..) ])
               (C [(sup k A B a f)..])).
Proof.
  destruct (ty_subst (wih n k A B C :: wbr k A B :: A :: G) s
              (wsup_ty k A B C) ds G (wih_val n k A B C s a f .: (f .: a ..))
              (sub_ok_wsup G k i j m n A B C s a f W Hik Hjk Hjn Hmn En
                 dAt dBt dCt dbr dih ds da df) (inhabits W)) as [d].
  replace ((wsup_ty k A B C) [wih_val n k A B C s a f .: (f .: a ..)])
     with (C [(sup k A B a f)..]) in d
     by (unfold wsup_ty, sh3; rasimpl; reflexivity).
  exact (inhabits d).
Qed.

(* ---- lookup: its functionality, its bound, and the type it finds ---- *)

Lemma lookup_len : forall i G A, lookup i G A -> i < length G.
Proof.
  intros i G A H; induction H as [G0 A0 | G0 i0 A0 B0 H0 IH]; cbn; lia.
Qed.

Lemma lookup_fun : forall i G A A', lookup i G A -> lookup i G A' -> A = A'.
Proof.
  intros i G A A' H; revert A'; induction H as [G0 A0 | G0 i0 A0 B0 H0 IH];
    intros A' H'; inversion H'; subst; [reflexivity |].
  f_equal; apply IH; assumption.
Qed.

Lemma lookup_ty : forall i G A, lookup i G A -> wfc G ->
  inhabited { k : nat & ty G A (UU k) }.
Proof.
  intros i G A Hl; induction Hl as [G0 A0 | G0 i0 A0 B0 Hl0 IH]; intros W.
  - inversion W; subst.
    match goal with
    | k : nat, d : ty G0 A0 (UU ?k0) |- _ =>
        destruct (ty_ren G0 A0 (UU k0) d (A0 :: G0) ↑
                    (ren_ok_shift G0 A0) (inhabits W)) as [d'];
        exact (inhabits (existT _ k0 d'))
    end.
  - inversion W; subst.
    destruct (IH ltac:(assumption)) as [[k0 d0]].
    destruct (ty_ren G0 A0 (UU k0) d0 (B0 :: G0) ↑
                (ren_ok_shift G0 B0) (inhabits W)) as [d'].
    exact (inhabits (existT _ k0 d')).
Qed.
