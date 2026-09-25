From CICM Require Import core unscoped Syntax.
From CICM Require Import Typing.Rules.
From Stdlib Require Import Arith Lia.

Import UnscopedNotations.
Open Scope list_scope.
Open Scope subst_scope.

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

Lemma ren_ok_shift G A : ren_ok shift G (A :: G).
Proof. intros i B H; apply lookup_S; exact H. Qed.

Lemma ren_ok_up xi G D A :
  ren_ok xi G D -> ren_ok (upRen_tm_tm xi) (A :: G) (A ⟨xi⟩ :: D).
Proof.
  intros H i B HB; inversion HB; subst.
  - replace ((A ⟨↑⟩) ⟨upRen_tm_tm xi⟩) with ((A ⟨xi⟩) ⟨↑⟩)
      by (asimpl; reflexivity).
    apply lookup_O.
  - match goal with
    | H0 : lookup ?i0 G ?A0 |- _ =>
        replace ((A0 ⟨↑⟩) ⟨upRen_tm_tm xi⟩) with ((A0 ⟨xi⟩) ⟨↑⟩)
          by (asimpl; reflexivity);
        apply lookup_S; apply H; exact H0
    end.
Qed.

Lemma nrec_succ_ren (C : tm) xi :
  (nrec_succ C) ⟨upRen_tm_tm (upRen_tm_tm xi)⟩ = nrec_succ (C ⟨upRen_tm_tm xi⟩).
Proof. unfold nrec_succ; asimpl; reflexivity. Qed.

Lemma nrec_succ_subst (C : tm) sigma :
  (nrec_succ C) [up_tm_tm (up_tm_tm sigma)] = nrec_succ (C [up_tm_tm sigma]).
Proof.
  unfold nrec_succ; asimpl.
  apply ext_tm; intros [| i]; asimpl; unfold funcomp;
    [reflexivity | exact (rinstInst'_tm (funcomp shift shift) (sigma i))].
Qed.

Lemma eta_ren (k : nat) (A B f : tm) xi :
  (lam k A B (app (A ⟨↑⟩) (B ⟨upRen_tm_tm shift⟩) (f ⟨↑⟩) (var_tm 0))) ⟨xi⟩
  = lam k (A ⟨xi⟩) (B ⟨upRen_tm_tm xi⟩)
      (app ((A ⟨xi⟩) ⟨↑⟩) ((B ⟨upRen_tm_tm xi⟩) ⟨upRen_tm_tm shift⟩)
           ((f ⟨xi⟩) ⟨↑⟩) (var_tm 0)).
Proof. asimpl; reflexivity. Qed.

Lemma eta_subst (k : nat) (A B f : tm) sigma :
  (lam k A B (app (A ⟨↑⟩) (B ⟨upRen_tm_tm shift⟩) (f ⟨↑⟩) (var_tm 0))) [sigma]
  = lam k (A [sigma]) (B [up_tm_tm sigma])
      (app ((A [sigma]) ⟨↑⟩) ((B [up_tm_tm sigma]) ⟨upRen_tm_tm shift⟩)
           ((f [sigma]) ⟨↑⟩) (var_tm 0)).
Proof. asimpl; reflexivity. Qed.

Lemma rec_succ_ren (C z s n : tm) xi :
  (s [ (natrec C z s n) .: n .. ]) ⟨xi⟩
  = (s ⟨upRen_tm_tm (upRen_tm_tm xi)⟩)
      [ (natrec (C ⟨upRen_tm_tm xi⟩) (z ⟨xi⟩)
           (s ⟨upRen_tm_tm (upRen_tm_tm xi)⟩) (n ⟨xi⟩)) .: (n ⟨xi⟩) .. ].
Proof. asimpl; reflexivity. Qed.

Lemma rec_succ_subst (C z s n : tm) sigma :
  (s [ (natrec C z s n) .: n .. ]) [sigma]
  = (s [up_tm_tm (up_tm_tm sigma)])
      [ (natrec (C [up_tm_tm sigma]) (z [sigma])
           (s [up_tm_tm (up_tm_tm sigma)]) (n [sigma])) .: (n [sigma]) .. ].
Proof. asimpl; reflexivity. Qed.

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
  - (* t_pi *) intros G k j A B Hjk dA IHA dB IHB D xi Hxi [wD].
    destruct (IHA D xi Hxi (inhabits wD)) as [dA'].
    destruct (IHB (A ⟨xi⟩ :: D) (upRen_tm_tm xi) (ren_ok_up xi G D A Hxi)
                (inhabits (w_cons D _ _ wD dA'))) as [dB'].
    exact (inhabits (t_pi D k j _ _ Hjk dA' dB')).
  - (* t_lam *) intros G k j A B t Hjk dA IHA dB IHB dt IHt D xi Hxi [wD].
    destruct (IHA D xi Hxi (inhabits wD)) as [dA'].
    pose proof (inhabits (w_cons D (A ⟨xi⟩) _ wD dA')) as wD'.
    destruct (IHB (A ⟨xi⟩ :: D) (upRen_tm_tm xi) (ren_ok_up xi G D A Hxi) wD') as [dB'].
    destruct (IHt (A ⟨xi⟩ :: D) (upRen_tm_tm xi) (ren_ok_up xi G D A Hxi) wD') as [dt'].
    exact (inhabits (t_lam D k j _ _ _ Hjk dA' dB' dt')).
  - (* t_app *) intros G k j A B f u Hjk dA IHA dB IHB df IHf du IHu D xi Hxi [wD].
    destruct (IHA D xi Hxi (inhabits wD)) as [dA'].
    destruct (IHB (A ⟨xi⟩ :: D) (upRen_tm_tm xi) (ren_ok_up xi G D A Hxi)
                (inhabits (w_cons D _ _ wD dA'))) as [dB'].
    destruct (IHf D xi Hxi (inhabits wD)) as [df'].
    destruct (IHu D xi Hxi (inhabits wD)) as [du'].
    replace ((B [u..]) ⟨xi⟩) with ((B ⟨upRen_tm_tm xi⟩) [(u ⟨xi⟩)..])
      by (asimpl; reflexivity).
    exact (inhabits (t_app D k j _ _ _ _ Hjk dA' dB' df' du')).
  - (* t_sig *) intros G k j A B Hjk dA IHA dB IHB D xi Hxi [wD].
    destruct (IHA D xi Hxi (inhabits wD)) as [dA'].
    destruct (IHB (A ⟨xi⟩ :: D) (upRen_tm_tm xi) (ren_ok_up xi G D A Hxi)
                (inhabits (w_cons D _ _ wD dA'))) as [dB'].
    exact (inhabits (t_sig D k j _ _ Hjk dA' dB')).
  - (* t_pair *) intros G k j A B t u Hjk dA IHA dB IHB dt IHt du IHu D xi Hxi [wD].
    destruct (IHA D xi Hxi (inhabits wD)) as [dA'].
    destruct (IHB (A ⟨xi⟩ :: D) (upRen_tm_tm xi) (ren_ok_up xi G D A Hxi)
                (inhabits (w_cons D _ _ wD dA'))) as [dB'].
    destruct (IHt D xi Hxi (inhabits wD)) as [dt'].
    destruct (IHu D xi Hxi (inhabits wD)) as [du'].
    replace ((B [t..]) ⟨xi⟩) with ((B ⟨upRen_tm_tm xi⟩) [(t ⟨xi⟩)..]) in du'
      by (asimpl; reflexivity).
    exact (inhabits (t_pair D k j _ _ _ _ Hjk dA' dB' dt' du')).
  - (* t_fst *) intros G k j A B p Hjk dA IHA dB IHB dp IHp D xi Hxi [wD].
    destruct (IHA D xi Hxi (inhabits wD)) as [dA'].
    destruct (IHB (A ⟨xi⟩ :: D) (upRen_tm_tm xi) (ren_ok_up xi G D A Hxi)
                (inhabits (w_cons D _ _ wD dA'))) as [dB'].
    destruct (IHp D xi Hxi (inhabits wD)) as [dp'].
    exact (inhabits (t_fst D k j _ _ _ Hjk dA' dB' dp')).
  - (* t_snd *) intros G k j A B p Hjk dA IHA dB IHB dp IHp D xi Hxi [wD].
    destruct (IHA D xi Hxi (inhabits wD)) as [dA'].
    destruct (IHB (A ⟨xi⟩ :: D) (upRen_tm_tm xi) (ren_ok_up xi G D A Hxi)
                (inhabits (w_cons D _ _ wD dA'))) as [dB'].
    destruct (IHp D xi Hxi (inhabits wD)) as [dp'].
    replace ((B [(fst A B p)..]) ⟨xi⟩)
      with ((B ⟨upRen_tm_tm xi⟩)
              [(fst (A ⟨xi⟩) (B ⟨upRen_tm_tm xi⟩) (p ⟨xi⟩))..])
      by (asimpl; reflexivity).
    exact (inhabits (t_snd D k j _ _ _ Hjk dA' dB' dp')).
  - (* t_nat *) intros G k W IHW D xi Hxi [wD]; exact (inhabits (t_nat D k wD)).
  - (* t_zero *) intros G k W IHW D xi Hxi [wD]; exact (inhabits (t_zero D k wD)).
  - (* t_succ *) intros G k n dn IHn D xi Hxi [wD].
    destruct (IHn D xi Hxi (inhabits wD)) as [dn'].
    exact (inhabits (t_succ D _ _ dn')).
  - (* t_natrec *) intros G C z s n k j dC IHC dz IHz ds IHs dn IHn D xi Hxi [wD].
    pose proof (w_cons D (nat_ j) j wD (t_nat D j wD)) as wDn.
    destruct (IHC (nat_ j :: D) (upRen_tm_tm xi) (ren_ok_up xi G D (nat_ j) Hxi)
                (inhabits wDn)) as [dC'].
    destruct (IHz D xi Hxi (inhabits wD)) as [dz'].
    destruct (IHs (C ⟨upRen_tm_tm xi⟩ :: nat_ j :: D)
                (upRen_tm_tm (upRen_tm_tm xi))
                (ren_ok_up (upRen_tm_tm xi) (nat_ j :: G) (nat_ j :: D) C
                   (ren_ok_up xi G D (nat_ j) Hxi))
                (inhabits (w_cons (nat_ j :: D) _ _ wDn dC'))) as [ds'].
    destruct (IHn D xi Hxi (inhabits wD)) as [dn'].
    replace ((C [(zero j)..]) ⟨xi⟩) with ((C ⟨upRen_tm_tm xi⟩) [(zero j)..]) in dz'
      by (asimpl; reflexivity).
    rewrite nrec_succ_ren in ds'.
    replace ((C [n..]) ⟨xi⟩) with ((C ⟨upRen_tm_tm xi⟩) [(n ⟨xi⟩)..])
      by (asimpl; reflexivity).
    exact (inhabits (t_natrec D _ _ _ _ k j dC' dz' ds' dn')).
  - (* t_prop *) intros G k W IHW D xi Hxi [wD]; exact (inhabits (t_prop D k wD)).
  - (* t_prf *) intros G k j p Hjk dp IHp D xi Hxi [wD].
    destruct (IHp D xi Hxi (inhabits wD)) as [dp'].
    exact (inhabits (t_prf D k j _ Hjk dp')).
  - (* t_all *) intros G A p j k dA IHA dp IHp D xi Hxi [wD].
    destruct (IHA D xi Hxi (inhabits wD)) as [dA'].
    destruct (IHp (A ⟨xi⟩ :: D) (upRen_tm_tm xi) (ren_ok_up xi G D A Hxi)
                (inhabits (w_cons D _ _ wD dA'))) as [dp'].
    exact (inhabits (t_all D _ _ j k dA' dp')).
  - (* t_all_intro *) intros G A p t j k dA IHA dp IHp dt IHt D xi Hxi [wD].
    destruct (IHA D xi Hxi (inhabits wD)) as [dA'].
    pose proof (inhabits (w_cons D (A ⟨xi⟩) _ wD dA')) as wD'.
    destruct (IHp (A ⟨xi⟩ :: D) (upRen_tm_tm xi) (ren_ok_up xi G D A Hxi) wD') as [dp'].
    destruct (IHt (A ⟨xi⟩ :: D) (upRen_tm_tm xi) (ren_ok_up xi G D A Hxi) wD') as [dt'].
    exact (inhabits (t_all_intro D _ _ _ j k dA' dp' dt')).
  - (* t_all_elim *) intros G A p f u j k dA IHA dp IHp df IHf du IHu D xi Hxi [wD].
    destruct (IHA D xi Hxi (inhabits wD)) as [dA'].
    destruct (IHp (A ⟨xi⟩ :: D) (upRen_tm_tm xi) (ren_ok_up xi G D A Hxi)
                (inhabits (w_cons D _ _ wD dA'))) as [dp'].
    destruct (IHf D xi Hxi (inhabits wD)) as [df'].
    destruct (IHu D xi Hxi (inhabits wD)) as [du'].
    replace ((prf j (p [u..])) ⟨xi⟩)
      with (prf j ((p ⟨upRen_tm_tm xi⟩) [(u ⟨xi⟩)..])) by (asimpl; reflexivity).
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
  - (* c_up_pi *) intros G k j A B Hjk dA IHA dB IHB D xi Hxi [wD].
    destruct (IHA D xi Hxi (inhabits wD)) as [dA'].
    destruct (IHB (A ⟨xi⟩ :: D) (upRen_tm_tm xi) (ren_ok_up xi G D A Hxi)
                (inhabits (w_cons D _ _ wD dA'))) as [dB'].
    exact (inhabits (c_up_pi D k j _ _ Hjk dA' dB')).
  - (* c_up_sig *) intros G k j A B Hjk dA IHA dB IHB D xi Hxi [wD].
    destruct (IHA D xi Hxi (inhabits wD)) as [dA'].
    destruct (IHB (A ⟨xi⟩ :: D) (upRen_tm_tm xi) (ren_ok_up xi G D A Hxi)
                (inhabits (w_cons D _ _ wD dA'))) as [dB'].
    exact (inhabits (c_up_sig D k j _ _ Hjk dA' dB')).
  - (* c_pi *) intros G k j A A' B B' Hjk dA IHA dB IHB dA' IHA' dB' IHB' cA IHcA cB IHcB
      D xi Hxi [wD].
    destruct (IHA D xi Hxi (inhabits wD)) as [d1].
    destruct (IHA' D xi Hxi (inhabits wD)) as [d3].
    destruct (IHB (A ⟨xi⟩ :: D) (upRen_tm_tm xi) (ren_ok_up xi G D A Hxi)
                (inhabits (w_cons D _ _ wD d1))) as [d2].
    destruct (IHB' (A' ⟨xi⟩ :: D) (upRen_tm_tm xi) (ren_ok_up xi G D A' Hxi)
                (inhabits (w_cons D _ _ wD d3))) as [d4].
    destruct (IHcA D xi Hxi (inhabits wD)) as [cA'].
    destruct (IHcB (A ⟨xi⟩ :: D) (upRen_tm_tm xi) (ren_ok_up xi G D A Hxi)
                (inhabits (w_cons D _ _ wD d1))) as [cB'].
    exact (inhabits (c_pi D k j _ _ _ _ Hjk d1 d2 d3 d4 cA' cB')).
  - (* c_lam *) intros G k j A A' B B' t t' Hjk dA IHA dB IHB dA' IHA' dB' IHB'
      cA IHcA cB IHcB dt IHt dt' IHt' ct IHct D xi Hxi [wD].
    destruct (IHA D xi Hxi (inhabits wD)) as [d1].
    destruct (IHA' D xi Hxi (inhabits wD)) as [d3].
    pose proof (ren_ok_up xi G D A Hxi) as Hup.
    pose proof (ren_ok_up xi G D A' Hxi) as Hup'.
    pose proof (inhabits (w_cons D (A ⟨xi⟩) _ wD d1)) as wD1.
    pose proof (inhabits (w_cons D (A' ⟨xi⟩) _ wD d3)) as wD2.
    destruct (IHB (A ⟨xi⟩ :: D) (upRen_tm_tm xi) Hup wD1) as [d2].
    destruct (IHB' (A' ⟨xi⟩ :: D) (upRen_tm_tm xi) Hup' wD2) as [d4].
    destruct (IHcA D xi Hxi (inhabits wD)) as [cA'].
    destruct (IHcB (A ⟨xi⟩ :: D) (upRen_tm_tm xi) Hup wD1) as [cB'].
    destruct (IHt (A ⟨xi⟩ :: D) (upRen_tm_tm xi) Hup wD1) as [d5].
    destruct (IHt' (A' ⟨xi⟩ :: D) (upRen_tm_tm xi) Hup' wD2) as [d6].
    destruct (IHct (A ⟨xi⟩ :: D) (upRen_tm_tm xi) Hup wD1) as [ct'].
    exact (inhabits (c_lam D k j _ _ _ _ _ _ Hjk d1 d2 d3 d4 cA' cB' d5 d6 ct')).
  - (* c_app *) intros G k j A B f f' u u' Hjk dA IHA dB IHB df IHf df' IHf' cf IHcf
      du IHu du' IHu' cu IHcu D xi Hxi [wD].
    destruct (IHA D xi Hxi (inhabits wD)) as [d1].
    destruct (IHB (A ⟨xi⟩ :: D) (upRen_tm_tm xi) (ren_ok_up xi G D A Hxi)
                (inhabits (w_cons D _ _ wD d1))) as [d2].
    destruct (IHf D xi Hxi (inhabits wD)) as [d3].
    destruct (IHf' D xi Hxi (inhabits wD)) as [d4].
    destruct (IHcf D xi Hxi (inhabits wD)) as [cf'].
    destruct (IHu D xi Hxi (inhabits wD)) as [d5].
    destruct (IHu' D xi Hxi (inhabits wD)) as [d6].
    destruct (IHcu D xi Hxi (inhabits wD)) as [cu'].
    replace ((B [u..]) ⟨xi⟩) with ((B ⟨upRen_tm_tm xi⟩) [(u ⟨xi⟩)..])
      by (asimpl; reflexivity).
    exact (inhabits (c_app D k j _ _ _ _ _ _ Hjk d1 d2 d3 d4 cf' d5 d6 cu')).
  - (* c_beta *) intros G k j A B t u Hjk dA IHA dB IHB dt IHt du IHu D xi Hxi [wD].
    destruct (IHA D xi Hxi (inhabits wD)) as [d1].
    pose proof (inhabits (w_cons D (A ⟨xi⟩) _ wD d1)) as wD'.
    destruct (IHB (A ⟨xi⟩ :: D) (upRen_tm_tm xi) (ren_ok_up xi G D A Hxi) wD') as [d2].
    destruct (IHt (A ⟨xi⟩ :: D) (upRen_tm_tm xi) (ren_ok_up xi G D A Hxi) wD') as [d3].
    destruct (IHu D xi Hxi (inhabits wD)) as [d4].
    replace ((B [u..]) ⟨xi⟩) with ((B ⟨upRen_tm_tm xi⟩) [(u ⟨xi⟩)..])
      by (asimpl; reflexivity).
    replace ((t [u..]) ⟨xi⟩) with ((t ⟨upRen_tm_tm xi⟩) [(u ⟨xi⟩)..])
      by (asimpl; reflexivity).
    exact (inhabits (c_beta D k j _ _ _ _ Hjk d1 d2 d3 d4)).
  - (* c_eta *) intros G k j A B f Hjk dA IHA dB IHB df IHf D xi Hxi [wD].
    destruct (IHA D xi Hxi (inhabits wD)) as [d1].
    destruct (IHB (A ⟨xi⟩ :: D) (upRen_tm_tm xi) (ren_ok_up xi G D A Hxi)
                (inhabits (w_cons D _ _ wD d1))) as [d2].
    destruct (IHf D xi Hxi (inhabits wD)) as [d3].
    rewrite eta_ren.
    exact (inhabits (c_eta D k j _ _ _ Hjk d1 d2 d3)).
  - (* c_sig *) intros G k j A A' B B' Hjk dA IHA dB IHB dA' IHA' dB' IHB' cA IHcA cB IHcB
      D xi Hxi [wD].
    destruct (IHA D xi Hxi (inhabits wD)) as [d1].
    destruct (IHA' D xi Hxi (inhabits wD)) as [d3].
    destruct (IHB (A ⟨xi⟩ :: D) (upRen_tm_tm xi) (ren_ok_up xi G D A Hxi)
                (inhabits (w_cons D _ _ wD d1))) as [d2].
    destruct (IHB' (A' ⟨xi⟩ :: D) (upRen_tm_tm xi) (ren_ok_up xi G D A' Hxi)
                (inhabits (w_cons D _ _ wD d3))) as [d4].
    destruct (IHcA D xi Hxi (inhabits wD)) as [cA'].
    destruct (IHcB (A ⟨xi⟩ :: D) (upRen_tm_tm xi) (ren_ok_up xi G D A Hxi)
                (inhabits (w_cons D _ _ wD d1))) as [cB'].
    exact (inhabits (c_sig D k j _ _ _ _ Hjk d1 d2 d3 d4 cA' cB')).
  - (* c_pair *) intros G k j A B t t' u u' Hjk dA IHA dB IHB dt IHt dt' IHt' ct IHct
      du IHu du' IHu' cu IHcu D xi Hxi [wD].
    destruct (IHA D xi Hxi (inhabits wD)) as [d1].
    destruct (IHB (A ⟨xi⟩ :: D) (upRen_tm_tm xi) (ren_ok_up xi G D A Hxi)
                (inhabits (w_cons D _ _ wD d1))) as [d2].
    destruct (IHt D xi Hxi (inhabits wD)) as [d3].
    destruct (IHt' D xi Hxi (inhabits wD)) as [d4].
    destruct (IHct D xi Hxi (inhabits wD)) as [ct'].
    destruct (IHu D xi Hxi (inhabits wD)) as [d5].
    destruct (IHu' D xi Hxi (inhabits wD)) as [d6].
    destruct (IHcu D xi Hxi (inhabits wD)) as [cu'].
    replace ((B [t..]) ⟨xi⟩) with ((B ⟨upRen_tm_tm xi⟩) [(t ⟨xi⟩)..]) in d5, d6, cu'
      by (asimpl; reflexivity).
    exact (inhabits (c_pair D k j _ _ _ _ _ _ Hjk d1 d2 d3 d4 ct' d5 d6 cu')).
  - (* c_fst *) intros G k j A B p p' Hjk dA IHA dB IHB dp IHp dp' IHp' cp IHcp
      D xi Hxi [wD].
    destruct (IHA D xi Hxi (inhabits wD)) as [d1].
    destruct (IHB (A ⟨xi⟩ :: D) (upRen_tm_tm xi) (ren_ok_up xi G D A Hxi)
                (inhabits (w_cons D _ _ wD d1))) as [d2].
    destruct (IHp D xi Hxi (inhabits wD)) as [d3].
    destruct (IHp' D xi Hxi (inhabits wD)) as [d4].
    destruct (IHcp D xi Hxi (inhabits wD)) as [cp'].
    exact (inhabits (c_fst D k j _ _ _ _ Hjk d1 d2 d3 d4 cp')).
  - (* c_snd *) intros G k j A B p p' Hjk dA IHA dB IHB dp IHp dp' IHp' cp IHcp
      D xi Hxi [wD].
    destruct (IHA D xi Hxi (inhabits wD)) as [d1].
    destruct (IHB (A ⟨xi⟩ :: D) (upRen_tm_tm xi) (ren_ok_up xi G D A Hxi)
                (inhabits (w_cons D _ _ wD d1))) as [d2].
    destruct (IHp D xi Hxi (inhabits wD)) as [d3].
    destruct (IHp' D xi Hxi (inhabits wD)) as [d4].
    destruct (IHcp D xi Hxi (inhabits wD)) as [cp'].
    replace ((B [(fst A B p)..]) ⟨xi⟩)
      with ((B ⟨upRen_tm_tm xi⟩)
              [(fst (A ⟨xi⟩) (B ⟨upRen_tm_tm xi⟩) (p ⟨xi⟩))..])
      by (asimpl; reflexivity).
    exact (inhabits (c_snd D k j _ _ _ _ Hjk d1 d2 d3 d4 cp')).
  - (* c_fst_beta *) intros G k j A B t u Hjk dA IHA dB IHB dt IHt du IHu D xi Hxi [wD].
    destruct (IHA D xi Hxi (inhabits wD)) as [d1].
    destruct (IHB (A ⟨xi⟩ :: D) (upRen_tm_tm xi) (ren_ok_up xi G D A Hxi)
                (inhabits (w_cons D _ _ wD d1))) as [d2].
    destruct (IHt D xi Hxi (inhabits wD)) as [d3].
    destruct (IHu D xi Hxi (inhabits wD)) as [d4].
    replace ((B [t..]) ⟨xi⟩) with ((B ⟨upRen_tm_tm xi⟩) [(t ⟨xi⟩)..]) in d4
      by (asimpl; reflexivity).
    exact (inhabits (c_fst_beta D k j _ _ _ _ Hjk d1 d2 d3 d4)).
  - (* c_snd_beta *) intros G k j A B t u Hjk dA IHA dB IHB dt IHt du IHu D xi Hxi [wD].
    destruct (IHA D xi Hxi (inhabits wD)) as [d1].
    destruct (IHB (A ⟨xi⟩ :: D) (upRen_tm_tm xi) (ren_ok_up xi G D A Hxi)
                (inhabits (w_cons D _ _ wD d1))) as [d2].
    destruct (IHt D xi Hxi (inhabits wD)) as [d3].
    destruct (IHu D xi Hxi (inhabits wD)) as [d4].
    replace ((B [t..]) ⟨xi⟩) with ((B ⟨upRen_tm_tm xi⟩) [(t ⟨xi⟩)..]) in d4 |- *
      by (asimpl; reflexivity).
    exact (inhabits (c_snd_beta D k j _ _ _ _ Hjk d1 d2 d3 d4)).
  - (* c_surj *) intros G k j A B p Hjk dA IHA dB IHB dp IHp D xi Hxi [wD].
    destruct (IHA D xi Hxi (inhabits wD)) as [d1].
    destruct (IHB (A ⟨xi⟩ :: D) (upRen_tm_tm xi) (ren_ok_up xi G D A Hxi)
                (inhabits (w_cons D _ _ wD d1))) as [d2].
    destruct (IHp D xi Hxi (inhabits wD)) as [d3].
    exact (inhabits (c_surj D k j _ _ _ Hjk d1 d2 d3)).
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
    destruct (IHC (nat_ j :: D) (upRen_tm_tm xi) Hxi1 (inhabits wDn)) as [d1].
    destruct (IHC' (nat_ j :: D) (upRen_tm_tm xi) Hxi1 (inhabits wDn)) as [d2].
    destruct (IHcC (nat_ j :: D) (upRen_tm_tm xi) Hxi1 (inhabits wDn)) as [cC'].
    destruct (IHz D xi Hxi (inhabits wD)) as [d3].
    destruct (IHz' D xi Hxi (inhabits wD)) as [d4].
    destruct (IHcz D xi Hxi (inhabits wD)) as [cz'].
    pose proof (ren_ok_up (upRen_tm_tm xi) (nat_ j :: G) (nat_ j :: D) C Hxi1) as Hxi2.
    pose proof (inhabits (w_cons (nat_ j :: D) (C ⟨upRen_tm_tm xi⟩) _ wDn d1)) as wDc.
    destruct (IHs (C ⟨upRen_tm_tm xi⟩ :: nat_ j :: D)
                (upRen_tm_tm (upRen_tm_tm xi)) Hxi2 wDc) as [d5].
    destruct (IHs' (C ⟨upRen_tm_tm xi⟩ :: nat_ j :: D)
                (upRen_tm_tm (upRen_tm_tm xi)) Hxi2 wDc) as [d6].
    destruct (IHcs (C ⟨upRen_tm_tm xi⟩ :: nat_ j :: D)
                (upRen_tm_tm (upRen_tm_tm xi)) Hxi2 wDc) as [cs'].
    destruct (IHn D xi Hxi (inhabits wD)) as [d7].
    destruct (IHn' D xi Hxi (inhabits wD)) as [d8].
    destruct (IHcn D xi Hxi (inhabits wD)) as [cn'].
    replace ((C [(zero j)..]) ⟨xi⟩) with ((C ⟨upRen_tm_tm xi⟩) [(zero j)..]) in d3, d4, cz'
      by (asimpl; reflexivity).
    rewrite nrec_succ_ren in d5, d6, cs'.
    replace ((C [n..]) ⟨xi⟩) with ((C ⟨upRen_tm_tm xi⟩) [(n ⟨xi⟩)..])
      by (asimpl; reflexivity).
    exact (inhabits (c_natrec D _ _ _ _ _ _ _ _ k j d1 d2 cC' d3 d4 cz'
                       d5 d6 cs' d7 d8 cn')).
  - (* c_rec_zero *) intros G C z s k j dC IHC dz IHz ds IHs D xi Hxi [wD].
    pose proof (w_cons D (nat_ j) j wD (t_nat D j wD)) as wDn.
    pose proof (ren_ok_up xi G D (nat_ j) Hxi) as Hxi1.
    destruct (IHC (nat_ j :: D) (upRen_tm_tm xi) Hxi1 (inhabits wDn)) as [d1].
    destruct (IHz D xi Hxi (inhabits wD)) as [d2].
    destruct (IHs (C ⟨upRen_tm_tm xi⟩ :: nat_ j :: D)
                (upRen_tm_tm (upRen_tm_tm xi))
                (ren_ok_up (upRen_tm_tm xi) (nat_ j :: G) (nat_ j :: D) C Hxi1)
                (inhabits (w_cons (nat_ j :: D) _ _ wDn d1))) as [d3].
    rewrite nrec_succ_ren in d3.
    replace ((C [(zero j)..]) ⟨xi⟩) with ((C ⟨upRen_tm_tm xi⟩) [(zero j)..]) in d2 |- *
      by (asimpl; reflexivity).
    exact (inhabits (c_rec_zero D _ _ _ k j d1 d2 d3)).
  - (* c_rec_succ *) intros G C z s n k j dC IHC dz IHz ds IHs dn IHn D xi Hxi [wD].
    pose proof (w_cons D (nat_ j) j wD (t_nat D j wD)) as wDn.
    pose proof (ren_ok_up xi G D (nat_ j) Hxi) as Hxi1.
    destruct (IHC (nat_ j :: D) (upRen_tm_tm xi) Hxi1 (inhabits wDn)) as [d1].
    destruct (IHz D xi Hxi (inhabits wD)) as [d2].
    destruct (IHs (C ⟨upRen_tm_tm xi⟩ :: nat_ j :: D)
                (upRen_tm_tm (upRen_tm_tm xi))
                (ren_ok_up (upRen_tm_tm xi) (nat_ j :: G) (nat_ j :: D) C Hxi1)
                (inhabits (w_cons (nat_ j :: D) _ _ wDn d1))) as [d3].
    destruct (IHn D xi Hxi (inhabits wD)) as [d4].
    rewrite nrec_succ_ren in d3.
    replace ((C [(zero j)..]) ⟨xi⟩) with ((C ⟨upRen_tm_tm xi⟩) [(zero j)..]) in d2
      by (asimpl; reflexivity).
    rewrite rec_succ_ren.
    replace ((C [(succ n)..]) ⟨xi⟩)
      with ((C ⟨upRen_tm_tm xi⟩) [(succ (n ⟨xi⟩))..]) by (asimpl; reflexivity).
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
    destruct (IHp (A ⟨xi⟩ :: D) (upRen_tm_tm xi) (ren_ok_up xi G D A Hxi)
                (inhabits (w_cons D _ _ wD d1))) as [d2].
    destruct (IHp' (A' ⟨xi⟩ :: D) (upRen_tm_tm xi) (ren_ok_up xi G D A' Hxi)
                (inhabits (w_cons D _ _ wD d3))) as [d4].
    destruct (IHcA D xi Hxi (inhabits wD)) as [cA'].
    destruct (IHcp (A ⟨xi⟩ :: D) (upRen_tm_tm xi) (ren_ok_up xi G D A Hxi)
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
  sub_ok (up_tm_tm sigma) (A :: G) (A [sigma] :: D).
Proof.
  intros i B HB; inversion HB; subst.
  - replace ((A ⟨↑⟩) [up_tm_tm sigma]) with ((A [sigma]) ⟨↑⟩)
      by (asimpl; reflexivity).
    exact (inhabits (t_var (A [sigma] :: D) 0 ((A [sigma]) ⟨↑⟩)
                       (w_cons D (A [sigma]) _ wD dA)
                       (lookup_O D (A [sigma])))).
  - match goal with
    | H0 : lookup ?i0 G ?A0 |- _ =>
        replace ((A0 ⟨↑⟩) [up_tm_tm sigma]) with ((A0 [sigma]) ⟨↑⟩)
          by (asimpl; reflexivity);
        destruct (H i0 A0 H0) as [d];
        exact (ty_ren D (sigma i0) (A0 [sigma]) d (A [sigma] :: D) shift
                 (ren_ok_shift D (A [sigma]))
                 (inhabits (w_cons D (A [sigma]) _ wD dA)))
    end.
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
  - (* t_pi *) intros G k j A B Hjk dA IHA dB IHB D sigma Hs [wD].
    destruct (IHA D sigma Hs (inhabits wD)) as [dA'].
    destruct (IHB (A [sigma] :: D) (up_tm_tm sigma) (sub_ok_up sigma G D A _ wD dA' Hs)
                (inhabits (w_cons D _ _ wD dA'))) as [dB'].
    exact (inhabits (t_pi D k j _ _ Hjk dA' dB')).
  - (* t_lam *) intros G k j A B t Hjk dA IHA dB IHB dt IHt D sigma Hs [wD].
    destruct (IHA D sigma Hs (inhabits wD)) as [dA'].
    pose proof (sub_ok_up sigma G D A _ wD dA' Hs) as Hs1.
    pose proof (inhabits (w_cons D (A [sigma]) _ wD dA')) as wD'.
    destruct (IHB (A [sigma] :: D) (up_tm_tm sigma) Hs1 wD') as [dB'].
    destruct (IHt (A [sigma] :: D) (up_tm_tm sigma) Hs1 wD') as [dt'].
    exact (inhabits (t_lam D k j _ _ _ Hjk dA' dB' dt')).
  - (* t_app *) intros G k j A B f u Hjk dA IHA dB IHB df IHf du IHu D sigma Hs [wD].
    destruct (IHA D sigma Hs (inhabits wD)) as [dA'].
    destruct (IHB (A [sigma] :: D) (up_tm_tm sigma) (sub_ok_up sigma G D A _ wD dA' Hs)
                (inhabits (w_cons D _ _ wD dA'))) as [dB'].
    destruct (IHf D sigma Hs (inhabits wD)) as [df'].
    destruct (IHu D sigma Hs (inhabits wD)) as [du'].
    replace ((B [u..]) [sigma]) with ((B [up_tm_tm sigma]) [(u [sigma])..])
      by (asimpl; reflexivity).
    exact (inhabits (t_app D k j _ _ _ _ Hjk dA' dB' df' du')).
  - (* t_sig *) intros G k j A B Hjk dA IHA dB IHB D sigma Hs [wD].
    destruct (IHA D sigma Hs (inhabits wD)) as [dA'].
    destruct (IHB (A [sigma] :: D) (up_tm_tm sigma) (sub_ok_up sigma G D A _ wD dA' Hs)
                (inhabits (w_cons D _ _ wD dA'))) as [dB'].
    exact (inhabits (t_sig D k j _ _ Hjk dA' dB')).
  - (* t_pair *) intros G k j A B t u Hjk dA IHA dB IHB dt IHt du IHu D sigma Hs [wD].
    destruct (IHA D sigma Hs (inhabits wD)) as [dA'].
    destruct (IHB (A [sigma] :: D) (up_tm_tm sigma) (sub_ok_up sigma G D A _ wD dA' Hs)
                (inhabits (w_cons D _ _ wD dA'))) as [dB'].
    destruct (IHt D sigma Hs (inhabits wD)) as [dt'].
    destruct (IHu D sigma Hs (inhabits wD)) as [du'].
    replace ((B [t..]) [sigma]) with ((B [up_tm_tm sigma]) [(t [sigma])..]) in du'
      by (asimpl; reflexivity).
    exact (inhabits (t_pair D k j _ _ _ _ Hjk dA' dB' dt' du')).
  - (* t_fst *) intros G k j A B p Hjk dA IHA dB IHB dp IHp D sigma Hs [wD].
    destruct (IHA D sigma Hs (inhabits wD)) as [dA'].
    destruct (IHB (A [sigma] :: D) (up_tm_tm sigma) (sub_ok_up sigma G D A _ wD dA' Hs)
                (inhabits (w_cons D _ _ wD dA'))) as [dB'].
    destruct (IHp D sigma Hs (inhabits wD)) as [dp'].
    exact (inhabits (t_fst D k j _ _ _ Hjk dA' dB' dp')).
  - (* t_snd *) intros G k j A B p Hjk dA IHA dB IHB dp IHp D sigma Hs [wD].
    destruct (IHA D sigma Hs (inhabits wD)) as [dA'].
    destruct (IHB (A [sigma] :: D) (up_tm_tm sigma) (sub_ok_up sigma G D A _ wD dA' Hs)
                (inhabits (w_cons D _ _ wD dA'))) as [dB'].
    destruct (IHp D sigma Hs (inhabits wD)) as [dp'].
    replace ((B [(fst A B p)..]) [sigma])
      with ((B [up_tm_tm sigma])
              [(fst (A [sigma]) (B [up_tm_tm sigma]) (p [sigma]))..])
      by (asimpl; reflexivity).
    exact (inhabits (t_snd D k j _ _ _ Hjk dA' dB' dp')).
  - (* t_nat *) intros G k W IHW D sigma Hs [wD]; exact (inhabits (t_nat D k wD)).
  - (* t_zero *) intros G k W IHW D sigma Hs [wD]; exact (inhabits (t_zero D k wD)).
  - (* t_succ *) intros G k n dn IHn D sigma Hs [wD].
    destruct (IHn D sigma Hs (inhabits wD)) as [dn'].
    exact (inhabits (t_succ D _ _ dn')).
  - (* t_natrec *) intros G C z s n k j dC IHC dz IHz ds IHs dn IHn D sigma Hs [wD].
    pose proof (w_cons D (nat_ j) j wD (t_nat D j wD)) as wDn.
    pose proof (sub_ok_up sigma G D (nat_ j) j wD (t_nat D j wD) Hs) as Hs1.
    destruct (IHC (nat_ j :: D) (up_tm_tm sigma) Hs1 (inhabits wDn)) as [dC'].
    destruct (IHz D sigma Hs (inhabits wD)) as [dz'].
    destruct (IHs (C [up_tm_tm sigma] :: nat_ j :: D) (up_tm_tm (up_tm_tm sigma))
                (sub_ok_up (up_tm_tm sigma) (nat_ j :: G) (nat_ j :: D) C _ wDn dC' Hs1)
                (inhabits (w_cons (nat_ j :: D) _ _ wDn dC'))) as [ds'].
    destruct (IHn D sigma Hs (inhabits wD)) as [dn'].
    replace ((C [(zero j)..]) [sigma]) with ((C [up_tm_tm sigma]) [(zero j)..]) in dz'
      by (asimpl; reflexivity).
    rewrite nrec_succ_subst in ds'.
    replace ((C [n..]) [sigma]) with ((C [up_tm_tm sigma]) [(n [sigma])..])
      by (asimpl; reflexivity).
    exact (inhabits (t_natrec D _ _ _ _ k j dC' dz' ds' dn')).
  - (* t_prop *) intros G k W IHW D sigma Hs [wD]; exact (inhabits (t_prop D k wD)).
  - (* t_prf *) intros G k j p Hjk dp IHp D sigma Hs [wD].
    destruct (IHp D sigma Hs (inhabits wD)) as [dp'].
    exact (inhabits (t_prf D k j _ Hjk dp')).
  - (* t_all *) intros G A p j k dA IHA dp IHp D sigma Hs [wD].
    destruct (IHA D sigma Hs (inhabits wD)) as [dA'].
    destruct (IHp (A [sigma] :: D) (up_tm_tm sigma) (sub_ok_up sigma G D A _ wD dA' Hs)
                (inhabits (w_cons D _ _ wD dA'))) as [dp'].
    exact (inhabits (t_all D _ _ j k dA' dp')).
  - (* t_all_intro *) intros G A p t j k dA IHA dp IHp dt IHt D sigma Hs [wD].
    destruct (IHA D sigma Hs (inhabits wD)) as [dA'].
    pose proof (sub_ok_up sigma G D A _ wD dA' Hs) as Hs1.
    pose proof (inhabits (w_cons D (A [sigma]) _ wD dA')) as wD'.
    destruct (IHp (A [sigma] :: D) (up_tm_tm sigma) Hs1 wD') as [dp'].
    destruct (IHt (A [sigma] :: D) (up_tm_tm sigma) Hs1 wD') as [dt'].
    exact (inhabits (t_all_intro D _ _ _ j k dA' dp' dt')).
  - (* t_all_elim *) intros G A p f u j k dA IHA dp IHp df IHf du IHu D sigma Hs [wD].
    destruct (IHA D sigma Hs (inhabits wD)) as [dA'].
    destruct (IHp (A [sigma] :: D) (up_tm_tm sigma) (sub_ok_up sigma G D A _ wD dA' Hs)
                (inhabits (w_cons D _ _ wD dA'))) as [dp'].
    destruct (IHf D sigma Hs (inhabits wD)) as [df'].
    destruct (IHu D sigma Hs (inhabits wD)) as [du'].
    replace ((prf j (p [u..])) [sigma])
      with (prf j ((p [up_tm_tm sigma]) [(u [sigma])..])) by (asimpl; reflexivity).
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
  - (* c_up_pi *) intros G k j A B Hjk dA IHA dB IHB D sigma Hs [wD].
    destruct (IHA D sigma Hs (inhabits wD)) as [dA'].
    destruct (IHB (A [sigma] :: D) (up_tm_tm sigma)
                (sub_ok_up sigma G D A j wD dA' Hs)
                (inhabits (w_cons D _ _ wD dA'))) as [dB'].
    exact (inhabits (c_up_pi D k j _ _ Hjk dA' dB')).
  - (* c_up_sig *) intros G k j A B Hjk dA IHA dB IHB D sigma Hs [wD].
    destruct (IHA D sigma Hs (inhabits wD)) as [dA'].
    destruct (IHB (A [sigma] :: D) (up_tm_tm sigma)
                (sub_ok_up sigma G D A j wD dA' Hs)
                (inhabits (w_cons D _ _ wD dA'))) as [dB'].
    exact (inhabits (c_up_sig D k j _ _ Hjk dA' dB')).
  - (* c_pi *) intros G k j A A' B B' Hjk dA IHA dB IHB dA' IHA' dB' IHB' cA IHcA cB IHcB
      D sigma Hs [wD].
    destruct (IHA D sigma Hs (inhabits wD)) as [d1].
    destruct (IHA' D sigma Hs (inhabits wD)) as [d3].
    pose proof (sub_ok_up sigma G D A _ wD d1 Hs) as Hs1.
    destruct (IHB (A [sigma] :: D) (up_tm_tm sigma) Hs1
                (inhabits (w_cons D _ _ wD d1))) as [d2].
    destruct (IHB' (A' [sigma] :: D) (up_tm_tm sigma)
                (sub_ok_up sigma G D A' _ wD d3 Hs)
                (inhabits (w_cons D _ _ wD d3))) as [d4].
    destruct (IHcA D sigma Hs (inhabits wD)) as [cA'].
    destruct (IHcB (A [sigma] :: D) (up_tm_tm sigma) Hs1
                (inhabits (w_cons D _ _ wD d1))) as [cB'].
    exact (inhabits (c_pi D k j _ _ _ _ Hjk d1 d2 d3 d4 cA' cB')).
  - (* c_lam *) intros G k j A A' B B' t t' Hjk dA IHA dB IHB dA' IHA' dB' IHB'
      cA IHcA cB IHcB dt IHt dt' IHt' ct IHct D sigma Hs [wD].
    destruct (IHA D sigma Hs (inhabits wD)) as [d1].
    destruct (IHA' D sigma Hs (inhabits wD)) as [d3].
    pose proof (sub_ok_up sigma G D A _ wD d1 Hs) as Hs1.
    pose proof (sub_ok_up sigma G D A' _ wD d3 Hs) as Hs2.
    pose proof (inhabits (w_cons D (A [sigma]) _ wD d1)) as wD1.
    pose proof (inhabits (w_cons D (A' [sigma]) _ wD d3)) as wD2.
    destruct (IHB (A [sigma] :: D) (up_tm_tm sigma) Hs1 wD1) as [d2].
    destruct (IHB' (A' [sigma] :: D) (up_tm_tm sigma) Hs2 wD2) as [d4].
    destruct (IHcA D sigma Hs (inhabits wD)) as [cA'].
    destruct (IHcB (A [sigma] :: D) (up_tm_tm sigma) Hs1 wD1) as [cB'].
    destruct (IHt (A [sigma] :: D) (up_tm_tm sigma) Hs1 wD1) as [d5].
    destruct (IHt' (A' [sigma] :: D) (up_tm_tm sigma) Hs2 wD2) as [d6].
    destruct (IHct (A [sigma] :: D) (up_tm_tm sigma) Hs1 wD1) as [ct'].
    exact (inhabits (c_lam D k j _ _ _ _ _ _ Hjk d1 d2 d3 d4 cA' cB' d5 d6 ct')).
  - (* c_app *) intros G k j A B f f' u u' Hjk dA IHA dB IHB df IHf df' IHf' cf IHcf
      du IHu du' IHu' cu IHcu D sigma Hs [wD].
    destruct (IHA D sigma Hs (inhabits wD)) as [d1].
    destruct (IHB (A [sigma] :: D) (up_tm_tm sigma) (sub_ok_up sigma G D A _ wD d1 Hs)
                (inhabits (w_cons D _ _ wD d1))) as [d2].
    destruct (IHf D sigma Hs (inhabits wD)) as [d3].
    destruct (IHf' D sigma Hs (inhabits wD)) as [d4].
    destruct (IHcf D sigma Hs (inhabits wD)) as [cf'].
    destruct (IHu D sigma Hs (inhabits wD)) as [d5].
    destruct (IHu' D sigma Hs (inhabits wD)) as [d6].
    destruct (IHcu D sigma Hs (inhabits wD)) as [cu'].
    replace ((B [u..]) [sigma]) with ((B [up_tm_tm sigma]) [(u [sigma])..])
      by (asimpl; reflexivity).
    exact (inhabits (c_app D k j _ _ _ _ _ _ Hjk d1 d2 d3 d4 cf' d5 d6 cu')).
  - (* c_beta *) intros G k j A B t u Hjk dA IHA dB IHB dt IHt du IHu D sigma Hs [wD].
    destruct (IHA D sigma Hs (inhabits wD)) as [d1].
    pose proof (sub_ok_up sigma G D A _ wD d1 Hs) as Hs1.
    pose proof (inhabits (w_cons D (A [sigma]) _ wD d1)) as wD'.
    destruct (IHB (A [sigma] :: D) (up_tm_tm sigma) Hs1 wD') as [d2].
    destruct (IHt (A [sigma] :: D) (up_tm_tm sigma) Hs1 wD') as [d3].
    destruct (IHu D sigma Hs (inhabits wD)) as [d4].
    replace ((B [u..]) [sigma]) with ((B [up_tm_tm sigma]) [(u [sigma])..])
      by (asimpl; reflexivity).
    replace ((t [u..]) [sigma]) with ((t [up_tm_tm sigma]) [(u [sigma])..])
      by (asimpl; reflexivity).
    exact (inhabits (c_beta D k j _ _ _ _ Hjk d1 d2 d3 d4)).
  - (* c_eta *) intros G k j A B f Hjk dA IHA dB IHB df IHf D sigma Hs [wD].
    destruct (IHA D sigma Hs (inhabits wD)) as [d1].
    destruct (IHB (A [sigma] :: D) (up_tm_tm sigma) (sub_ok_up sigma G D A _ wD d1 Hs)
                (inhabits (w_cons D _ _ wD d1))) as [d2].
    destruct (IHf D sigma Hs (inhabits wD)) as [d3].
    rewrite eta_subst.
    exact (inhabits (c_eta D k j _ _ _ Hjk d1 d2 d3)).
  - (* c_sig *) intros G k j A A' B B' Hjk dA IHA dB IHB dA' IHA' dB' IHB' cA IHcA cB IHcB
      D sigma Hs [wD].
    destruct (IHA D sigma Hs (inhabits wD)) as [d1].
    destruct (IHA' D sigma Hs (inhabits wD)) as [d3].
    pose proof (sub_ok_up sigma G D A _ wD d1 Hs) as Hs1.
    destruct (IHB (A [sigma] :: D) (up_tm_tm sigma) Hs1
                (inhabits (w_cons D _ _ wD d1))) as [d2].
    destruct (IHB' (A' [sigma] :: D) (up_tm_tm sigma)
                (sub_ok_up sigma G D A' _ wD d3 Hs)
                (inhabits (w_cons D _ _ wD d3))) as [d4].
    destruct (IHcA D sigma Hs (inhabits wD)) as [cA'].
    destruct (IHcB (A [sigma] :: D) (up_tm_tm sigma) Hs1
                (inhabits (w_cons D _ _ wD d1))) as [cB'].
    exact (inhabits (c_sig D k j _ _ _ _ Hjk d1 d2 d3 d4 cA' cB')).
  - (* c_pair *) intros G k j A B t t' u u' Hjk dA IHA dB IHB dt IHt dt' IHt' ct IHct
      du IHu du' IHu' cu IHcu D sigma Hs [wD].
    destruct (IHA D sigma Hs (inhabits wD)) as [d1].
    destruct (IHB (A [sigma] :: D) (up_tm_tm sigma) (sub_ok_up sigma G D A _ wD d1 Hs)
                (inhabits (w_cons D _ _ wD d1))) as [d2].
    destruct (IHt D sigma Hs (inhabits wD)) as [d3].
    destruct (IHt' D sigma Hs (inhabits wD)) as [d4].
    destruct (IHct D sigma Hs (inhabits wD)) as [ct'].
    destruct (IHu D sigma Hs (inhabits wD)) as [d5].
    destruct (IHu' D sigma Hs (inhabits wD)) as [d6].
    destruct (IHcu D sigma Hs (inhabits wD)) as [cu'].
    replace ((B [t..]) [sigma]) with ((B [up_tm_tm sigma]) [(t [sigma])..])
      in d5, d6, cu' by (asimpl; reflexivity).
    exact (inhabits (c_pair D k j _ _ _ _ _ _ Hjk d1 d2 d3 d4 ct' d5 d6 cu')).
  - (* c_fst *) intros G k j A B p p' Hjk dA IHA dB IHB dp IHp dp' IHp' cp IHcp
      D sigma Hs [wD].
    destruct (IHA D sigma Hs (inhabits wD)) as [d1].
    destruct (IHB (A [sigma] :: D) (up_tm_tm sigma) (sub_ok_up sigma G D A _ wD d1 Hs)
                (inhabits (w_cons D _ _ wD d1))) as [d2].
    destruct (IHp D sigma Hs (inhabits wD)) as [d3].
    destruct (IHp' D sigma Hs (inhabits wD)) as [d4].
    destruct (IHcp D sigma Hs (inhabits wD)) as [cp'].
    exact (inhabits (c_fst D k j _ _ _ _ Hjk d1 d2 d3 d4 cp')).
  - (* c_snd *) intros G k j A B p p' Hjk dA IHA dB IHB dp IHp dp' IHp' cp IHcp
      D sigma Hs [wD].
    destruct (IHA D sigma Hs (inhabits wD)) as [d1].
    destruct (IHB (A [sigma] :: D) (up_tm_tm sigma) (sub_ok_up sigma G D A _ wD d1 Hs)
                (inhabits (w_cons D _ _ wD d1))) as [d2].
    destruct (IHp D sigma Hs (inhabits wD)) as [d3].
    destruct (IHp' D sigma Hs (inhabits wD)) as [d4].
    destruct (IHcp D sigma Hs (inhabits wD)) as [cp'].
    replace ((B [(fst A B p)..]) [sigma])
      with ((B [up_tm_tm sigma])
              [(fst (A [sigma]) (B [up_tm_tm sigma]) (p [sigma]))..])
      by (asimpl; reflexivity).
    exact (inhabits (c_snd D k j _ _ _ _ Hjk d1 d2 d3 d4 cp')).
  - (* c_fst_beta *) intros G k j A B t u Hjk dA IHA dB IHB dt IHt du IHu D sigma Hs [wD].
    destruct (IHA D sigma Hs (inhabits wD)) as [d1].
    destruct (IHB (A [sigma] :: D) (up_tm_tm sigma) (sub_ok_up sigma G D A _ wD d1 Hs)
                (inhabits (w_cons D _ _ wD d1))) as [d2].
    destruct (IHt D sigma Hs (inhabits wD)) as [d3].
    destruct (IHu D sigma Hs (inhabits wD)) as [d4].
    replace ((B [t..]) [sigma]) with ((B [up_tm_tm sigma]) [(t [sigma])..]) in d4
      by (asimpl; reflexivity).
    exact (inhabits (c_fst_beta D k j _ _ _ _ Hjk d1 d2 d3 d4)).
  - (* c_snd_beta *) intros G k j A B t u Hjk dA IHA dB IHB dt IHt du IHu D sigma Hs [wD].
    destruct (IHA D sigma Hs (inhabits wD)) as [d1].
    destruct (IHB (A [sigma] :: D) (up_tm_tm sigma) (sub_ok_up sigma G D A _ wD d1 Hs)
                (inhabits (w_cons D _ _ wD d1))) as [d2].
    destruct (IHt D sigma Hs (inhabits wD)) as [d3].
    destruct (IHu D sigma Hs (inhabits wD)) as [d4].
    replace ((B [t..]) [sigma]) with ((B [up_tm_tm sigma]) [(t [sigma])..])
      in d4 |- * by (asimpl; reflexivity).
    exact (inhabits (c_snd_beta D k j _ _ _ _ Hjk d1 d2 d3 d4)).
  - (* c_surj *) intros G k j A B p Hjk dA IHA dB IHB dp IHp D sigma Hs [wD].
    destruct (IHA D sigma Hs (inhabits wD)) as [d1].
    destruct (IHB (A [sigma] :: D) (up_tm_tm sigma) (sub_ok_up sigma G D A _ wD d1 Hs)
                (inhabits (w_cons D _ _ wD d1))) as [d2].
    destruct (IHp D sigma Hs (inhabits wD)) as [d3].
    exact (inhabits (c_surj D k j _ _ _ Hjk d1 d2 d3)).
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
    destruct (IHC (nat_ j :: D) (up_tm_tm sigma) Hs1 (inhabits wDn)) as [d1].
    destruct (IHC' (nat_ j :: D) (up_tm_tm sigma) Hs1 (inhabits wDn)) as [d2].
    destruct (IHcC (nat_ j :: D) (up_tm_tm sigma) Hs1 (inhabits wDn)) as [cC'].
    destruct (IHz D sigma Hs (inhabits wD)) as [d3].
    destruct (IHz' D sigma Hs (inhabits wD)) as [d4].
    destruct (IHcz D sigma Hs (inhabits wD)) as [cz'].
    pose proof (sub_ok_up (up_tm_tm sigma) (nat_ j :: G) (nat_ j :: D) C _ wDn d1 Hs1)
      as Hs2.
    pose proof (inhabits (w_cons (nat_ j :: D) (C [up_tm_tm sigma]) _ wDn d1)) as wDc.
    destruct (IHs (C [up_tm_tm sigma] :: nat_ j :: D) (up_tm_tm (up_tm_tm sigma))
                Hs2 wDc) as [d5].
    destruct (IHs' (C [up_tm_tm sigma] :: nat_ j :: D) (up_tm_tm (up_tm_tm sigma))
                Hs2 wDc) as [d6].
    destruct (IHcs (C [up_tm_tm sigma] :: nat_ j :: D) (up_tm_tm (up_tm_tm sigma))
                Hs2 wDc) as [cs'].
    destruct (IHn D sigma Hs (inhabits wD)) as [d7].
    destruct (IHn' D sigma Hs (inhabits wD)) as [d8].
    destruct (IHcn D sigma Hs (inhabits wD)) as [cn'].
    replace ((C [(zero j)..]) [sigma]) with ((C [up_tm_tm sigma]) [(zero j)..])
      in d3, d4, cz' by (asimpl; reflexivity).
    rewrite nrec_succ_subst in d5, d6, cs'.
    replace ((C [n..]) [sigma]) with ((C [up_tm_tm sigma]) [(n [sigma])..])
      by (asimpl; reflexivity).
    exact (inhabits (c_natrec D _ _ _ _ _ _ _ _ k j d1 d2 cC' d3 d4 cz'
                       d5 d6 cs' d7 d8 cn')).
  - (* c_rec_zero *) intros G C z s k j dC IHC dz IHz ds IHs D sigma Hs [wD].
    pose proof (w_cons D (nat_ j) j wD (t_nat D j wD)) as wDn.
    pose proof (sub_ok_up sigma G D (nat_ j) j wD (t_nat D j wD) Hs) as Hs1.
    destruct (IHC (nat_ j :: D) (up_tm_tm sigma) Hs1 (inhabits wDn)) as [d1].
    destruct (IHz D sigma Hs (inhabits wD)) as [d2].
    destruct (IHs (C [up_tm_tm sigma] :: nat_ j :: D) (up_tm_tm (up_tm_tm sigma))
                (sub_ok_up (up_tm_tm sigma) (nat_ j :: G) (nat_ j :: D) C _ wDn d1 Hs1)
                (inhabits (w_cons (nat_ j :: D) _ _ wDn d1))) as [d3].
    rewrite nrec_succ_subst in d3.
    replace ((C [(zero j)..]) [sigma]) with ((C [up_tm_tm sigma]) [(zero j)..])
      in d2 |- * by (asimpl; reflexivity).
    exact (inhabits (c_rec_zero D _ _ _ k j d1 d2 d3)).
  - (* c_rec_succ *) intros G C z s n k j dC IHC dz IHz ds IHs dn IHn D sigma Hs [wD].
    pose proof (w_cons D (nat_ j) j wD (t_nat D j wD)) as wDn.
    pose proof (sub_ok_up sigma G D (nat_ j) j wD (t_nat D j wD) Hs) as Hs1.
    destruct (IHC (nat_ j :: D) (up_tm_tm sigma) Hs1 (inhabits wDn)) as [d1].
    destruct (IHz D sigma Hs (inhabits wD)) as [d2].
    destruct (IHs (C [up_tm_tm sigma] :: nat_ j :: D) (up_tm_tm (up_tm_tm sigma))
                (sub_ok_up (up_tm_tm sigma) (nat_ j :: G) (nat_ j :: D) C _ wDn d1 Hs1)
                (inhabits (w_cons (nat_ j :: D) _ _ wDn d1))) as [d3].
    destruct (IHn D sigma Hs (inhabits wD)) as [d4].
    rewrite nrec_succ_subst in d3.
    replace ((C [(zero j)..]) [sigma]) with ((C [up_tm_tm sigma]) [(zero j)..]) in d2
      by (asimpl; reflexivity).
    rewrite rec_succ_subst.
    replace ((C [(succ n)..]) [sigma])
      with ((C [up_tm_tm sigma]) [(succ (n [sigma]))..]) by (asimpl; reflexivity).
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
    destruct (IHp (A [sigma] :: D) (up_tm_tm sigma) Hs1
                (inhabits (w_cons D _ _ wD d1))) as [d2].
    destruct (IHp' (A' [sigma] :: D) (up_tm_tm sigma)
                (sub_ok_up sigma G D A' _ wD d3 Hs)
                (inhabits (w_cons D _ _ wD d3))) as [d4].
    destruct (IHcA D sigma Hs (inhabits wD)) as [cA'].
    destruct (IHcp (A [sigma] :: D) (up_tm_tm sigma) Hs1
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
  - replace ((A ⟨↑⟩) [u..]) with A by (asimpl; reflexivity).
    exact (inhabits du).
  - match goal with
    | H0 : lookup ?i0 G ?T0 |- _ =>
        replace ((T0 ⟨↑⟩) [u..]) with T0 by (asimpl; reflexivity);
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
        destruct (ty_ren G0 A0 (UU k0) d (A0 :: G0) shift
                    (ren_ok_shift G0 A0) (inhabits W)) as [d'];
        exact (inhabits (existT _ k0 d'))
    end.
  - inversion W; subst.
    destruct (IH ltac:(assumption)) as [[k0 d0]].
    destruct (ty_ren G0 A0 (UU k0) d0 (B0 :: G0) shift
                (ren_ok_shift G0 B0) (inhabits W)) as [d'].
    exact (inhabits (existT _ k0 d')).
Qed.
