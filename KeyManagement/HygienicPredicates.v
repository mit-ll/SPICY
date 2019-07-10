From Coq Require Import
     List
     Morphisms
     Eqdep
     (* Program.Equality (* for dependent induction *) *)
.

Require Import
        MyPrelude
        Maps
        Common
        MapLtac
        Keys
        Tactics.

Require Import
        RealWorld.

Set Implicit Arguments.



Inductive protocol_hygienic (cs : list cipher_id): forall {A}, user_cmd A -> Prop :=
| BindRecvHygienic :
    forall {A t} (rec : user_cmd (message t)) (cmd : message t -> user_cmd A) pat,
      rec = Recv pat
      -> (forall cs' msg,
            cs' = match msg with
                  | SignedCiphertext _ _ c_id => c_id :: cs
                  | _ => cs
                  end
            -> protocol_hygienic cs' (cmd msg))
      -> protocol_hygienic cs (Bind rec cmd)
| BindHygienic : forall {A B} (rec : user_cmd B) (cmd : B -> user_cmd A) b,
    protocol_hygienic cs (cmd b)
    -> protocol_hygienic cs (Bind rec cmd)
| ReturnHygienic : forall {A} (a : A),
    protocol_hygienic cs (Return a)
| GenHygienic :
    protocol_hygienic cs Gen
| SendHygienic : forall {t} (uid : user_id) (msg : message t),
    protocol_hygienic cs (Send uid msg)
| RecvHygienic : forall {t} pat,
    protocol_hygienic cs (@Recv t pat)
| SignEncryptHygienic : forall {t} (msg : message t) k__s k__e,
    protocol_hygienic cs (SignEncrypt k__s k__e msg)
| DecryptHygienic : forall {t} msg k__s k__e c_id,
    msg = SignedCiphertext k__s k__e c_id
    -> List.In c_id cs
    -> protocol_hygienic cs (@Decrypt t msg).
