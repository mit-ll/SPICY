{-# OPTIONS_GHC -cpp -XMagicHash #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module ExampleProtocols where

import qualified Prelude
import qualified Common
import qualified Datatypes
import qualified Keys
import qualified Maps
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

coq_A :: Common.Coq_user_id
coq_A =
  0

coq_B :: Common.Coq_user_id
coq_B =
  Prelude.succ 0

mkrUsr :: Keys.Coq_key_perms -> RealWorld.Coq_user_cmd -> RealWorld.Coq_user_data
mkrUsr ks p =
  RealWorld.Coq_mkUserData ks p ([]) ([]) ([]) ([]) 0

mkrU :: Keys.Coq_keys -> Keys.Coq_key_perms -> Keys.Coq_key_perms -> RealWorld.Coq_user_cmd -> RealWorld.Coq_user_cmd ->
        RealWorld.Coq_user_data -> RealWorld.Coq_universe
mkrU gks keys__a keys__b p__a p__b adv =
  RealWorld.Coq_mkUniverse
    (Maps._NatMap__Map__add coq_B (mkrUsr keys__b p__b) (Maps._NatMap__Map__add coq_A (mkrUsr keys__a p__a) Maps._NatMap__Map__empty)) adv
    Maps._NatMap__Map__empty gks

_SignPingSendProtocol__coq_KID1 :: Keys.Coq_key_identifier
_SignPingSendProtocol__coq_KID1 =
  0

_SignPingSendProtocol__coq_KEY1 :: Keys.Coq_key
_SignPingSendProtocol__coq_KEY1 =
  Keys.MkCryptoKey _SignPingSendProtocol__coq_KID1 Keys.Signing Keys.AsymKey

_SignPingSendProtocol__coq_KEYS :: Maps.NatMap__Map__Coq_t Keys.Coq_key
_SignPingSendProtocol__coq_KEYS =
  Maps._NatMap__Map__add _SignPingSendProtocol__coq_KID1 _SignPingSendProtocol__coq_KEY1 Maps._NatMap__Map__empty

_SignPingSendProtocol__coq_A__keys :: Maps.NatMap__Map__Coq_t Prelude.Bool
_SignPingSendProtocol__coq_A__keys =
  Maps._NatMap__Map__add _SignPingSendProtocol__coq_KID1 Prelude.True Maps._NatMap__Map__empty

_SignPingSendProtocol__coq_B__keys :: Maps.NatMap__Map__Coq_t Prelude.Bool
_SignPingSendProtocol__coq_B__keys =
  Maps._NatMap__Map__add _SignPingSendProtocol__coq_KID1 Prelude.False Maps._NatMap__Map__empty

_SignPingSendProtocol__real_univ_start :: RealWorld.Coq_user_data -> RealWorld.Coq_universe
_SignPingSendProtocol__real_univ_start =
  mkrU _SignPingSendProtocol__coq_KEYS _SignPingSendProtocol__coq_A__keys _SignPingSendProtocol__coq_B__keys (RealWorld.Bind (RealWorld.Base
    Messages.Nat) (RealWorld.Base Messages.Nat) RealWorld.Gen (\n -> RealWorld.Bind (RealWorld.Base Messages.Nat) (RealWorld.Crypto
    Messages.Nat) (RealWorld.Sign Messages.Nat _SignPingSendProtocol__coq_KID1 coq_B (RealWorld.Coq_message__Content (unsafeCoerce n))) (\c ->
    RealWorld.Bind (RealWorld.Base Messages.Nat) (RealWorld.Base Messages.Unit) (RealWorld.Send Messages.Nat coq_B (unsafeCoerce c)) (\_ ->
    RealWorld.Return (RealWorld.Base Messages.Nat) n)))) (RealWorld.Bind (RealWorld.Base Messages.Nat) (RealWorld.Crypto Messages.Nat)
    (RealWorld.Recv Messages.Nat (RealWorld.Signed _SignPingSendProtocol__coq_KID1 Prelude.True)) (\c -> RealWorld.Bind (RealWorld.Base
    Messages.Nat) (RealWorld.UPair (RealWorld.Base Messages.Bool) (RealWorld.Message Messages.Nat)) (RealWorld.Verify Messages.Nat
    _SignPingSendProtocol__coq_KID1 (unsafeCoerce c)) (\v -> RealWorld.Return (RealWorld.Base Messages.Nat)
    (case Datatypes.fst (unsafeCoerce v) of {
      Prelude.True -> case Datatypes.snd (unsafeCoerce v) of {
                       RealWorld.Coq_message__Content p -> unsafeCoerce p;
                       _ -> unsafeCoerce 0};
      Prelude.False -> unsafeCoerce (Prelude.succ 0)}))))

