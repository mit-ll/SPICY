{-# OPTIONS_GHC -cpp -XMagicHash #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module ProtocolExtraction where

import qualified Prelude
import qualified Datatypes
import qualified ExampleProtocols
import qualified Keys
import qualified Messages
import qualified RealWorld

#ifdef __GLASGOW_HASKELL__
import qualified GHC.Base
#else
-- HUGS
import qualified IOExts
#endif

#ifdef __GLASGOW_HASKELL__
unsafeCoerce :: a -> b
unsafeCoerce = GHC.Base.unsafeCoerce#
#else
-- HUGS
unsafeCoerce :: a -> b
unsafeCoerce = IOExts.unsafeCoerce
#endif

akeys :: ([]) ((,) Keys.Coq_key_identifier Prelude.Bool)
akeys =
  (:) ((,) ExampleProtocols._SignPingSendProtocol__coq_KID1 Prelude.True) ([])

bkeys :: ([]) ((,) Keys.Coq_key_identifier Prelude.Bool)
bkeys =
  (:) ((,) ExampleProtocols._SignPingSendProtocol__coq_KID1 Prelude.False) ([])

userProto1 :: RealWorld.Coq_user_cmd
userProto1 =
  RealWorld.Bind (RealWorld.Base Messages.Nat) (RealWorld.Base Messages.Nat) RealWorld.Gen (\n ->
    RealWorld.Bind (RealWorld.Base Messages.Nat) (RealWorld.Crypto Messages.Nat) (RealWorld.Sign
    Messages.Nat ExampleProtocols._SignPingSendProtocol__coq_KID1 ExampleProtocols.coq_B
    (RealWorld.Coq_message__Content (unsafeCoerce n))) (\c -> RealWorld.Bind (RealWorld.Base
    Messages.Nat) (RealWorld.Base Messages.Unit) (RealWorld.Send Messages.Nat ExampleProtocols.coq_B
    (unsafeCoerce c)) (\_ -> RealWorld.Return (RealWorld.Base Messages.Nat) n)))

userProto2 :: RealWorld.Coq_user_cmd
userProto2 =
  RealWorld.Bind (RealWorld.Base Messages.Nat) (RealWorld.Crypto Messages.Nat) (RealWorld.Recv
    Messages.Nat (RealWorld.Signed ExampleProtocols._SignPingSendProtocol__coq_KID1 Prelude.True)) (\c ->
    RealWorld.Bind (RealWorld.Base Messages.Nat) (RealWorld.UPair (RealWorld.Base Messages.Bool)
    (RealWorld.Message Messages.Nat)) (RealWorld.Verify Messages.Nat
    ExampleProtocols._SignPingSendProtocol__coq_KID1 (unsafeCoerce c)) (\v -> RealWorld.Return
    (RealWorld.Base Messages.Nat)
    (case Datatypes.fst (unsafeCoerce v) of {
      Prelude.True ->
       case Datatypes.snd (unsafeCoerce v) of {
        RealWorld.Coq_message__Content p -> unsafeCoerce p;
        _ -> unsafeCoerce 0};
      Prelude.False -> unsafeCoerce (Prelude.succ 0)})))

simpleSendProto :: (,) (([]) Keys.Coq_key)
                   (([]) ((,) (([]) ((,) Keys.Coq_key_identifier Prelude.Bool)) RealWorld.Coq_user_cmd))
simpleSendProto =
  (,) ((:) ExampleProtocols._SignPingSendProtocol__coq_KEY1 ([])) ((:) ((,) akeys userProto1) ((:) ((,)
    bkeys userProto2) ([])))

coq_KEY1 :: Keys.Coq_key
coq_KEY1 =
  Keys.MkCryptoKey 0 Keys.Signing Keys.AsymKey

coq_KEY2 :: Keys.Coq_key
coq_KEY2 =
  Keys.MkCryptoKey (Prelude.succ 0) Keys.Signing Keys.AsymKey

secprotokeysa :: ([]) ((,) Prelude.Int Prelude.Bool)
secprotokeysa =
  (:) ((,) 0 Prelude.True) ((:) ((,) (Prelude.succ 0) Prelude.False) ([]))

secprotokeysb :: ([]) ((,) Prelude.Int Prelude.Bool)
secprotokeysb =
  (:) ((,) 0 Prelude.False) ((:) ((,) (Prelude.succ 0) Prelude.True) ([]))

secprotoUsera :: RealWorld.Coq_user_cmd
secprotoUsera =
  RealWorld.Bind (RealWorld.Base Messages.Nat) (RealWorld.Base Messages.Access)
    (RealWorld.GenerateAsymKey Keys.Encryption) (\kp -> RealWorld.Bind (RealWorld.Base Messages.Nat)
    (RealWorld.Crypto Messages.Access) (RealWorld.Sign Messages.Access 0 ExampleProtocols.coq_B
    (RealWorld.Coq_message__Permission ((,) (Datatypes.fst (unsafeCoerce kp)) Prelude.False))) (\c1 ->
    RealWorld.Bind (RealWorld.Base Messages.Nat) (RealWorld.Base Messages.Unit) (RealWorld.Send
    Messages.Access ExampleProtocols.coq_B (unsafeCoerce c1)) (\_ -> RealWorld.Bind (RealWorld.Base
    Messages.Nat) (RealWorld.Crypto Messages.Nat) (RealWorld.Recv Messages.Nat (RealWorld.SignedEncrypted
    (Prelude.succ 0) (Datatypes.fst (unsafeCoerce kp)) Prelude.True)) (\c2 -> RealWorld.Bind
    (RealWorld.Base Messages.Nat) (RealWorld.Message Messages.Nat) (RealWorld.Decrypt Messages.Nat
    (unsafeCoerce c2)) (\m -> RealWorld.Return (RealWorld.Base Messages.Nat)
    (unsafeCoerce RealWorld._Coq_message__extractContent m))))))

secprotoUserb :: RealWorld.Coq_user_cmd
secprotoUserb =
  RealWorld.Bind (RealWorld.Base Messages.Nat) (RealWorld.Crypto Messages.Access) (RealWorld.Recv
    Messages.Access (RealWorld.Signed 0 Prelude.True)) (\c1 -> RealWorld.Bind (RealWorld.Base
    Messages.Nat) (RealWorld.UPair (RealWorld.Base Messages.Bool) (RealWorld.Message Messages.Access))
    (RealWorld.Verify Messages.Access 0 (unsafeCoerce c1)) (\v -> RealWorld.Bind (RealWorld.Base
    Messages.Nat) (RealWorld.Base Messages.Nat) RealWorld.Gen (\n -> RealWorld.Bind (RealWorld.Base
    Messages.Nat) (RealWorld.Crypto Messages.Nat) (RealWorld.SignEncrypt Messages.Nat (Prelude.succ 0)
    (Datatypes.fst (RealWorld._Coq_message__extractPermission (Datatypes.snd (unsafeCoerce v))))
    ExampleProtocols.coq_A (RealWorld.Coq_message__Content (unsafeCoerce n))) (\c2 -> RealWorld.Bind
    (RealWorld.Base Messages.Nat) (RealWorld.Base Messages.Unit) (RealWorld.Send Messages.Nat
    ExampleProtocols.coq_A (unsafeCoerce c2)) (\_ -> RealWorld.Return (RealWorld.Base Messages.Nat)
    n)))))

shareSecretProto :: (,) (([]) Keys.Coq_key)
                    (([]) ((,) (([]) ((,) Prelude.Int Prelude.Bool)) RealWorld.Coq_user_cmd))
shareSecretProto =
  (,) ((:) coq_KEY1 ((:) coq_KEY2 ([]))) ((:) ((,) secprotokeysa secprotoUsera) ((:) ((,) secprotokeysb
    secprotoUserb) ([])))

