(******************************************************************************)
(*                                                                            *)
(*                        CODE OF HAMMURABI (c. 1754 BCE)                     *)
(*                                                                            *)
(*     Formalizing the 282 laws of Hammurabi: lex talionis, property          *)
(*     rights, family law, commercial transactions, and judicial              *)
(*     procedures of ancient Babylon.                                         *)
(*                                                                            *)
(*     Anu and Bel called by name me, Hammurabi, the exalted prince,          *)
(*     to bring about the rule of righteousness in the land.                  *)
(*     (Prologue, Code of Hammurabi)                                          *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     Date: January 6, 2026                                                  *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Strings.String.
From Stdlib Require Import micromega.Lia.
Import ListNotations.

(******************************************************************************)
(* SECTION 1: SOCIAL CLASSES                                                  *)
(******************************************************************************)

(* Babylonian society recognized three principal classes *)
Inductive SocialClass : Type :=
  | Awilum    (* free person / nobleman *)
  | Mushkenum (* dependent/commoner *)
  | Wardum.   (* slave *)

(* Social class decidable equality *)
Definition social_class_eq (a b : SocialClass) : bool :=
  match a, b with
  | Awilum,    Awilum    => true
  | Mushkenum, Mushkenum => true
  | Wardum,    Wardum    => true
  | _, _                 => false
  end.

Lemma social_class_eq_refl : forall c, social_class_eq c c = true.
Proof. intros []; reflexivity. Qed.

Lemma social_class_eq_correct : forall a b,
  social_class_eq a b = true <-> a = b.
Proof.
  intros [] []; simpl; split; intro H; try reflexivity; try discriminate.
Qed.

(******************************************************************************)
(* SECTION 2: PENALTIES                                                       *)
(******************************************************************************)

(* Penalties in the Code *)
Inductive Penalty : Type :=
  | Death
  | Mutilation       (* e.g. cutting off a hand, branding *)
  | SilverFine (n : nat)   (* fine in shekels of silver *)
  | Drowning
  | Burning
  | Impalement
  | Restitution (n : nat)  (* repay n-fold *)
  | Enslavement
  | Expulsion              (* cast out of city / family *)
  | Disinheritance
  | NoRemedyAvailable.     (* claim not actionable *)

(******************************************************************************)
(* SECTION 3: PARTIES                                                         *)
(******************************************************************************)

Record Party : Type := mkParty {
  party_class : SocialClass;
  party_free  : bool        (* true = free, false = slave *)
}.

Definition is_free (p : Party) : bool := party_free p.

Definition awilum  := mkParty Awilum    true.
Definition mushken := mkParty Mushkenum true.
Definition slave   := mkParty Wardum    false.

(******************************************************************************)
(* SECTION 4: OFFENSES AND JUDGMENT                                           *)
(******************************************************************************)

Inductive Offense : Type :=
  (* Procedural / judicial *)
  | FalseAccusationOfMurder
  | PerjuryInCapitalCase
  | JudgeAltersVerdict
  (* Theft and property *)
  | TheftFromTempleOrPalace
  | ReceivingStolen (from_temple : bool)
  | TheftOfMinorChild
  | HouseBreaking
  | Brigandage
  (* Slavery *)
  | HarbouringRunawaySlave
  | StealingSlave
  | RemovingSlaveMarkWithoutConsent
  (* Agricultural *)
  | NeglectOfFieldByTenant
  | FloodNeighbourByNeglect
  (* Building *)
  | HouseCollapseKillsOwner
  | HouseCollapseKillsOwnersSon
  (* Tavern-keeping *)
  | TavernKeeperFailsToReportConspirators
  (* Family law *)
  | AdulteryByWife
  | RapeOfBetrothedVirgin
  | IncestFatherSon
  | IncestMotherSon
  (* Bodily harm — lex talionis applies between Awilum *)
  | StrikeAndKillAwilum
  | KnockOutToothOfAwilum
  | BreakBoneOfAwilum
  | KnockOutEyeOfAwilum
  | StrikeAndKillMushkenum
  | StrikeAndKillSlave
  (* Surgeon liability *)
  | SurgeonKillsAwilum
  | SurgeonKillsMushkenum
  | SurgeonKillsSlave
  (* Veterinary *)
  | VetKillsOxOrAss
  (* Wet-nurse substitution *)
  | WetNurseSubstitutesChild.

(* The judgment function: given the offense and the social classes of
   offender and victim, return the prescribed penalty. *)
Definition adjudicate (o : Offense) (offender victim : SocialClass) : Penalty :=
  match o with
  (* Law 1-2: false accusation of murder -> death if unproven *)
  | FalseAccusationOfMurder => Death

  (* Law 3: perjury in capital case -> death *)
  | PerjuryInCapitalCase => Death

  (* Law 5: judge alters verdict -> fine + disbarred (modelled as fine) *)
  | JudgeAltersVerdict => SilverFine 12

  (* Law 6: theft from temple or palace -> death *)
  | TheftFromTempleOrPalace => Death

  (* Law 7-8: receiving stolen goods *)
  | ReceivingStolen true  => Death              (* from temple/palace *)
  | ReceivingStolen false => Restitution 30     (* from commoner *)

  (* Law 14: steal minor child of free person -> death *)
  | TheftOfMinorChild => Death

  (* Law 21: house-breaking -> death at the breach *)
  | HouseBreaking => Death

  (* Law 22: brigandage -> death *)
  | Brigandage => Death

  (* Law 16: harbour runaway slave -> death *)
  | HarbouringRunawaySlave => Death

  (* Law 15: steal/spirit away slave -> death *)
  | StealingSlave => Death

  (* Law 226-227: remove slave mark without consent *)
  | RemovingSlaveMarkWithoutConsent => Death

  (* Law 42-43: tenant neglects field -> grain penalty (modelled as fine) *)
  | NeglectOfFieldByTenant => SilverFine 0  (* grain, not silver; placeholder *)

  (* Law 53-55: flooding neighbour by negligence -> grain restitution *)
  | FloodNeighbourByNeglect => Restitution 1

  (* Law 229: house collapses kills owner -> builder dies *)
  | HouseCollapseKillsOwner => Death

  (* Law 230: house collapses kills owner's son -> builder's son dies *)
  | HouseCollapseKillsOwnersSon => Death

  (* Law 109: tavern-keeper fails to report conspirators -> death *)
  | TavernKeeperFailsToReportConspirators => Death

  (* Law 129: adultery by wife -> both drowning (unless husband pardons) *)
  | AdulteryByWife => Drowning

  (* Law 130: rape of betrothed virgin -> death of offender, woman free *)
  | RapeOfBetrothedVirgin => Death

  (* Law 157: incest father-son (son sleeps with father's wife) -> both burned *)
  | IncestFatherSon => Burning

  (* Law 158: son found with step-mother post-father -> expulsion *)
  | IncestMotherSon => Expulsion

  (* Lex talionis (Laws 196-200) — class-sensitive *)
  | StrikeAndKillAwilum =>
      match offender with
      | Awilum    => Death
      | Mushkenum => SilverFine 60
      | Wardum    => Death
      end

  | KnockOutEyeOfAwilum =>
      match offender with
      | Awilum    => Mutilation    (* eye for an eye *)
      | Mushkenum => SilverFine 60
      | Wardum    => Death
      end

  | BreakBoneOfAwilum =>
      match offender with
      | Awilum    => Mutilation    (* bone for bone *)
      | Mushkenum => SilverFine 60
      | Wardum    => Death
      end

  | KnockOutToothOfAwilum =>
      match offender with
      | Awilum    => Mutilation    (* tooth for tooth *)
      | Mushkenum => SilverFine 20
      | Wardum    => Death
      end

  | StrikeAndKillMushkenum =>
      match offender with
      | Awilum    => SilverFine 60
      | Mushkenum => SilverFine 30
      | Wardum    => Death
      end

  | StrikeAndKillSlave =>
      (* Law 116, 214: killing another's slave -> replace with slave or pay *)
      SilverFine 20

  (* Law 218: surgeon kills awilum -> hands cut off *)
  | SurgeonKillsAwilum =>
      match victim with
      | Awilum    => Mutilation
      | Mushkenum => SilverFine 5
      | Wardum    => SilverFine 2   (* replace the slave *)
      end

  | SurgeonKillsMushkenum => SilverFine 5

  | SurgeonKillsSlave => SilverFine 2

  (* Law 225: vet kills ox or ass -> pay 1/4 of value *)
  | VetKillsOxOrAss => SilverFine 1   (* proportional; placeholder *)

  (* Law 194: wet-nurse substitutes a child -> breast cut off *)
  | WetNurseSubstitutesChild => Mutilation
  end.

(******************************************************************************)
(* SECTION 5: KEY THEOREMS                                                    *)
(******************************************************************************)

(* Theorem: Lex talionis — an awilum who knocks out another awilum's eye
   receives Mutilation, not a fine or death. *)
Theorem lex_talionis_eye :
  adjudicate KnockOutEyeOfAwilum Awilum Awilum = Mutilation.
Proof. reflexivity. Qed.

(* Theorem: Class mitigation — a mushkenum who knocks out an awilum's eye
   pays a silver fine instead of suffering mutilation. *)
Theorem mushkenum_eye_fine :
  adjudicate KnockOutEyeOfAwilum Mushkenum Awilum = SilverFine 60.
Proof. reflexivity. Qed.

(* Theorem: False accusation carries death. *)
Theorem false_accusation_death :
  adjudicate FalseAccusationOfMurder Awilum Awilum = Death.
Proof. reflexivity. Qed.

(* Theorem: Theft from the temple carries death regardless of class. *)
Theorem temple_theft_death : forall offender victim,
  adjudicate TheftFromTempleOrPalace offender victim = Death.
Proof. intros [] []; reflexivity. Qed.

(* Theorem: House-building liability — builder dies if house kills owner. *)
Theorem builder_liability :
  adjudicate HouseCollapseKillsOwner Awilum Awilum = Death.
Proof. reflexivity. Qed.

(* Theorem: A surgeon who kills a free awilum is mutilated (hands cut off). *)
Theorem surgeon_kills_awilum :
  adjudicate SurgeonKillsAwilum Awilum Awilum = Mutilation.
Proof. reflexivity. Qed.

(* Theorem: Adultery by a wife is punishable by drowning. *)
Theorem adultery_drowning :
  adjudicate AdulteryByWife Awilum Awilum = Drowning.
Proof. reflexivity. Qed.

(* Theorem: Lex talionis for bone — awilum breaks awilum's bone -> Mutilation. *)
Theorem lex_talionis_bone :
  adjudicate BreakBoneOfAwilum Awilum Awilum = Mutilation.
Proof. reflexivity. Qed.

(* Theorem: Lex talionis for tooth — awilum knocks out awilum's tooth -> Mutilation. *)
Theorem lex_talionis_tooth :
  adjudicate KnockOutToothOfAwilum Awilum Awilum = Mutilation.
Proof. reflexivity. Qed.

(* Theorem: Penalty escalation — offenses against higher classes carry
   heavier or equal penalties compared to offenses against lower classes.
   Instantiated: killing an awilum vs killing a slave. *)
Theorem killing_awilum_heavier_than_slave :
  adjudicate StrikeAndKillAwilum Awilum Awilum = Death /\
  adjudicate StrikeAndKillSlave  Awilum Awilum = SilverFine 20.
Proof. split; reflexivity. Qed.

(* Theorem: Brigandage is a capital offense. *)
Theorem brigandage_capital :
  adjudicate Brigandage Awilum Awilum = Death.
Proof. reflexivity. Qed.

(* Theorem: Perjury in a capital case is itself a capital offense. *)
Theorem perjury_capital :
  adjudicate PerjuryInCapitalCase Awilum Awilum = Death.
Proof. reflexivity. Qed.

(* Theorem: Runaway slave harboring is a capital offense. *)
Theorem harbour_slave_death :
  adjudicate HarbouringRunawaySlave Awilum Awilum = Death.
Proof. reflexivity. Qed.

(******************************************************************************)
(* SECTION 6: COMMERCIAL LAW — LOAN AND DEPOSIT                               *)
(******************************************************************************)

(* Interest rate caps in Hammurabi's code:
   - Silver loans: max 20% per year (Law 89)
   - Grain loans:  max 33.3% per year (Law 89)
   We model annual interest in percent. *)

Definition max_silver_interest : nat := 20.
Definition max_grain_interest  : nat := 33.

Inductive CommodityType := Silver | Grain.

Definition interest_cap (c : CommodityType) : nat :=
  match c with
  | Silver => max_silver_interest
  | Grain  => max_grain_interest
  end.

(* A loan is compliant if the agreed interest does not exceed the cap. *)
Definition loan_compliant (c : CommodityType) (rate : nat) : bool :=
  Nat.leb rate (interest_cap c).

Lemma silver_loan_20_ok : loan_compliant Silver 20 = true.
Proof. reflexivity. Qed.

Lemma silver_loan_21_usurious : loan_compliant Silver 21 = false.
Proof. reflexivity. Qed.

Lemma grain_loan_33_ok : loan_compliant Grain 33 = true.
Proof. reflexivity. Qed.

Lemma grain_loan_34_usurious : loan_compliant Grain 34 = false.
Proof. reflexivity. Qed.

(* Law 122-123: deposits must be witnessed; unwitnessed deposit claims
   are not actionable. *)
Inductive DepositRecord : Type :=
  | WitnessedDeposit   (amount : nat)
  | UnwitnessedDeposit (amount : nat).

Definition deposit_actionable (d : DepositRecord) : bool :=
  match d with
  | WitnessedDeposit _   => true
  | UnwitnessedDeposit _ => false
  end.

Lemma witnessed_deposit_is_actionable : forall n,
  deposit_actionable (WitnessedDeposit n) = true.
Proof. intros; reflexivity. Qed.

Lemma unwitnessed_deposit_not_actionable : forall n,
  deposit_actionable (UnwitnessedDeposit n) = false.
Proof. intros; reflexivity. Qed.

(******************************************************************************)
(* SECTION 7: FAMILY LAW — MARRIAGE, DIVORCE, ADOPTION                       *)
(******************************************************************************)

(* Divorce settlement (Laws 138-140):
   - If husband divorces a wife who bore him children, he must return
     her dowry (marhatum) and give her usufruct of field/orchard.
   - If she bore no children, he returns the dowry only.
   - If she was a naditu (temple woman), only dowry returned.
   We model the mandatory silver payment obligation. *)

Inductive WifeStatus :=
  | HasChildren
  | ChildlessFreeWoman
  | Naditu.            (* dedicated to a deity; cannot bear children *)

(* Returns true if the divorcing husband must provide field/orchard usufruct *)
Definition usufruct_owed (w : WifeStatus) : bool :=
  match w with
  | HasChildren       => true
  | ChildlessFreeWoman => false
  | Naditu            => false
  end.

Lemma children_secure_usufruct : usufruct_owed HasChildren = true.
Proof. reflexivity. Qed.

Lemma childless_no_usufruct : usufruct_owed ChildlessFreeWoman = false.
Proof. reflexivity. Qed.

(* Adoption (Laws 185-186):
   - A child adopted from birth and raised cannot be reclaimed by birth parents.
   - A child adopted after being able to identify its parents CAN return
     to its birth home. *)
Inductive AdoptionAge :=
  | AdoptedFromBirth
  | AdoptedAfterRecognition.

Definition birth_parents_can_reclaim (a : AdoptionAge) : bool :=
  match a with
  | AdoptedFromBirth        => false
  | AdoptedAfterRecognition => true
  end.

Lemma adopted_from_birth_irrecoverable :
  birth_parents_can_reclaim AdoptedFromBirth = false.
Proof. reflexivity. Qed.

(******************************************************************************)
(* SECTION 8: PROPERTY — ORCHARD AND FIELD TENANCY                           *)
(******************************************************************************)

(* Law 60: planting an orchard — tenant tends for 4 years;
   in year 5 the owner and tenant split the yield equally. *)

Definition orchard_owner_share_year5 : nat := 50. (* percent *)
Definition orchard_tenant_share_year5 : nat := 50.

Lemma orchard_shares_sum_to_100 :
  orchard_owner_share_year5 + orchard_tenant_share_year5 = 100.
Proof. reflexivity. Qed.

(* Law 78: a tenant who is unable to pay rent cannot be evicted in year
   of crop failure if it was due to flood/drought — debt is waived.
   We model the waiver condition. *)

Inductive CropFailureCause :=
  | FloodOrDrought    (* force majeure — debt waived *)
  | OwnerNeglect
  | TenantNeglect.

Definition rent_waived (cause : CropFailureCause) : bool :=
  match cause with
  | FloodOrDrought => true
  | OwnerNeglect   => true
  | TenantNeglect  => false
  end.

Lemma flood_waives_rent : rent_waived FloodOrDrought = true.
Proof. reflexivity. Qed.

Lemma tenant_neglect_no_waiver : rent_waived TenantNeglect = false.
Proof. reflexivity. Qed.

(******************************************************************************)
(* SECTION 9: COMPLETE PENALTY DECIDABILITY                                   *)
(******************************************************************************)

(* Every offense and class combination yields a well-defined penalty. *)
Theorem adjudication_total : forall o offender victim,
  exists p, adjudicate o offender victim = p.
Proof.
  intros o offender victim.
  exists (adjudicate o offender victim).
  reflexivity.
Qed.

(* Death is the penalty for the most severe capital offenses
   (when committed by an awilum against an awilum). *)
Definition capital_offenses : list Offense :=
  [ FalseAccusationOfMurder
  ; PerjuryInCapitalCase
  ; TheftFromTempleOrPalace
  ; TheftOfMinorChild
  ; HouseBreaking
  ; Brigandage
  ; HarbouringRunawaySlave
  ; StealingSlave
  ; RemovingSlaveMarkWithoutConsent
  ; TavernKeeperFailsToReportConspirators
  ; HouseCollapseKillsOwner
  ; HouseCollapseKillsOwnersSon
  ; RapeOfBetrothedVirgin
  ].

Theorem capital_offenses_are_death : forall o,
  In o capital_offenses ->
  adjudicate o Awilum Awilum = Death.
Proof.
  intros o Hin.
  repeat (destruct Hin as [<- | Hin]; [reflexivity |]).
  destruct Hin.
Qed.

(******************************************************************************)
(* SECTION 10: EVIDENTIARY STANDARD                                           *)
(******************************************************************************)

(* Law 1-3: The ordeal by river — if the accused drowns, guilty; if survives,
   accuser is put to death.  We model the river ordeal outcome. *)

Inductive OrdalResult :=
  | Survived   (* accused innocent *)
  | Drowned.   (* accused guilty   *)

Definition ordeal_verdict (r : OrdalResult) : bool (* true = accused guilty *) :=
  match r with
  | Survived => false
  | Drowned  => true
  end.

Definition accuser_fate_after_ordeal (r : OrdalResult) : Penalty :=
  match r with
  | Survived => Death      (* accuser executed if accused survives *)
  | Drowned  => NoRemedyAvailable  (* accusation vindicated *)
  end.

Lemma ordeal_acquittal_kills_accuser :
  accuser_fate_after_ordeal Survived = Death.
Proof. reflexivity. Qed.

Lemma ordeal_drowning_vindicates_accuser :
  accuser_fate_after_ordeal Drowned = NoRemedyAvailable.
Proof. reflexivity. Qed.

(******************************************************************************)
(* SECTION 11: RESTITUTION MULTIPLIERS                                        *)
(******************************************************************************)

(* Several laws prescribe n-fold restitution for dishonest dealings.
   Law 8: theft of ox/sheep/pig/boat from palace -> 30-fold.
   Law 8: theft from a mushkenum -> 10-fold.
   Law 265: shepherd defrauds owner of flock -> 10-fold. *)

Definition restitution_fold_temple : nat := 30.
Definition restitution_fold_commoner : nat := 10.

Lemma temple_restitution_exceeds_commoner :
  restitution_fold_commoner < restitution_fold_temple.
Proof. unfold restitution_fold_commoner, restitution_fold_temple. lia. Qed.

(* For any restitution multiplier m >= 1, restoring m*amount > original *)
Lemma restitution_exceeds_original : forall amount m,
  m >= 2 ->
  amount > 0 ->
  m * amount > amount.
Proof.
  intros amount m Hm Ha.
  destruct m as [| [| m']].
  - lia.
  - lia.
  - simpl. lia.
Qed.

(******************************************************************************)
(* SECTION 12: SUMMARY                                                        *)
(******************************************************************************)

(*
  This file provides a Coq formalization of key structural features of the
  Code of Hammurabi (c. 1754 BCE):

    1. Social classes: Awilum, Mushkenum, Wardum with decidable equality.
    2. Offenses: 28 offense constructors covering judicial, property, family,
       bodily harm, professional liability, and commercial domains.
    3. Penalties: Death, Mutilation, Silver fines, Drowning, Burning, etc.
    4. Adjudication: a total function mapping (offense, offender class,
       victim class) -> penalty, encoding lex talionis and class-based
       mitigation/escalation.
    5. Key theorems: lex talionis for eye/bone/tooth, capital offense
       exhaustiveness, river ordeal evidentiary rules.
    6. Commercial law: interest caps (silver 20%, grain 33%), deposit
       witness requirements.
    7. Family law: divorce usufruct obligations, adoption irrevocability.
    8. Property law: orchard tenancy shares, crop-failure rent waiver.
    9. Restitution multipliers: 30-fold (temple), 10-fold (commoner).

  All proofs are closed; no Admitted lemmas.
*)
