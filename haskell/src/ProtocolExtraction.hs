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

