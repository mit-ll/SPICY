{-# OPTIONS_GHC -cpp -XMagicHash #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module ProtocolExtraction where

import qualified Prelude
import qualified ExampleProtocols
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

coq_UserProto1 :: RealWorld.Coq_user_cmd
coq_UserProto1 =
  RealWorld.Bind (RealWorld.Base Messages.Nat) (RealWorld.Base Messages.Nat) RealWorld.Gen (\n -> RealWorld.Bind
    (RealWorld.Base Messages.Nat) (RealWorld.Crypto Messages.Nat) (RealWorld.Sign Messages.Nat
    ExampleProtocols._SignPingSendProtocol__coq_KID1 ExampleProtocols.coq_B (RealWorld.Coq_message__Content
    (unsafeCoerce n))) (\c -> RealWorld.Bind (RealWorld.Base Messages.Nat) (RealWorld.Base Messages.Unit)
    (RealWorld.Send Messages.Nat ExampleProtocols.coq_B (unsafeCoerce c)) (\_ -> RealWorld.Return (RealWorld.Base
    Messages.Nat) n)))

