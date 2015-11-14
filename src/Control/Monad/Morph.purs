-- | A port of Haskell's [mmorph library](http://hackage.haskell.org/package/mmorph-1.0.0/docs/Control-Monad-Morph.html)
module Control.Monad.Morph where

import Prelude

import Control.Monad.Trans (MonadTrans, lift)
import qualified Control.Monad.Cont.Trans as C
import qualified Control.Monad.Except.Trans as E
import qualified Control.Monad.Maybe.Trans as M
import qualified Control.Monad.Reader.Trans as R
import qualified Control.Monad.RWS.Trans as RWS
import qualified Control.Monad.State.Trans as S
import qualified Control.Monad.Writer.Trans as W
import qualified Control.Monad.List.Trans as L
import qualified Control.Monad.Free.Trans as F

import Data.Monoid (Monoid)
import Data.Either (Either(Left, Right))
import Data.Maybe (Maybe(Just, Nothing))
import Data.Functor.Compose (Compose(Compose))
import Data.Identity (runIdentity, Identity(Identity))
import Data.Functor.Product (Product(Product))
import Data.Functor.Coproduct (Coproduct(Coproduct))
import Data.Tuple (Tuple(Tuple))
import Data.NaturalTransformation (Natural())

class MInvariant t where
  ihoist :: forall m n. (Monad m, Monad n) => Natural m n -> Natural n m -> Natural (t m) (t n)

ihoistF :: forall t m n. (MFunctor t, Monad m) => Natural m n -> Natural n m -> Natural (t m) (t n)
ihoistF f _ = hoist f

instance minvariantContT :: MInvariant (C.ContT r) where
  ihoist f g a = C.ContT \cont -> f (C.runContT a (g <<< cont))

instance minvariantExceptT :: MInvariant (E.ExceptT e) where
  ihoist = ihoistF

-- instance minvariantListT :: MInvariant L.ListT where
  --hoist = ihoistF

instance minvariantMaybeT :: MInvariant M.MaybeT where
  ihoist = ihoistF

instance minvariantReaderT :: MInvariant (R.ReaderT r) where
  ihoist = ihoistF

instance minvariantWriterT :: MInvariant (W.WriterT w) where
  ihoist = ihoistF

instance minvariantStateT :: MInvariant (S.StateT s) where
  ihoist = ihoistF

instance minvariantRWST :: MInvariant (RWS.RWST r w s) where
  ihoist = ihoistF

instance minvariantCompose :: (Functor f) => MInvariant (Compose f) where
  ihoist = ihoistF

instance minvariantProduct :: MInvariant (Product f) where
  ihoist = ihoistF

instance minvariantCoproduct :: MInvariant (Coproduct f) where
  ihoist = ihoistF

instance minvariantFreeT :: (Functor f) => MInvariant (F.FreeT f) where
  ihoist f _ = F.hoistFreeT f

class MFunctor t where
  hoist :: forall m n. (Monad m) => Natural m n -> Natural (t m) (t n)

instance mfunctorExceptT :: MFunctor (E.ExceptT e) where
  hoist nat m = E.ExceptT (nat (E.runExceptT m))

--instance mfunctorListT :: MFunctor L.ListT where
  --hoist nat m = L.ListT (nat (L.runListT m))

instance mfunctorMaybeT :: MFunctor M.MaybeT where
  hoist nat m = M.MaybeT (nat (M.runMaybeT m))

instance mfunctorReaderT :: MFunctor (R.ReaderT r) where
  hoist nat m = R.ReaderT (\ i -> nat (R.runReaderT m i))

instance mfunctorWriterT :: MFunctor (W.WriterT w) where
  hoist nat m = W.WriterT (nat (W.runWriterT m))

instance mfunctorStateT :: MFunctor (S.StateT s) where
  hoist nat m = S.StateT (\ s -> nat (S.runStateT m s))

instance mfunctorRWST :: MFunctor (RWS.RWST r w s) where
  hoist nat m = RWS.RWST (\ r s -> nat (RWS.runRWST m r s))

instance mfunctorCompose :: (Functor f) => MFunctor (Compose f) where
  hoist nat (Compose f) = Compose (map nat f)

instance mfunctorProduct :: MFunctor (Product f) where
  hoist nat (Product (Tuple f g)) = Product (Tuple f (nat g))

instance mfunctorCoproduct :: MFunctor (Coproduct f) where
  hoist nat (Coproduct a) = Coproduct (map nat a)

generalize :: forall m a. (Monad m) => Identity a -> m a
generalize = pure <<< runIdentity

class (MFunctor t, MonadTrans t) <= MMonad t where
  embed :: forall n m b. (Monad n) => (forall a. m a -> t n a) -> t m b -> t n b

squash :: forall a m t. (Monad m, MMonad t) => t (t m) a -> t m a
squash = embed id

infixr 2 >|>
infixr 2 =<|
infixl 2 <|<
infixl 2 |>=

(>|>) :: forall m1 m2 m3 t c. (MMonad t, Monad m3) => (forall a. m1 a -> t m2 a)
                                                   -> (forall b. m2 b -> t m3 b)
                                                   ->            m1 c -> t m3 c
(>|>) f g m = embed g (f m)

(<|<) :: forall m1 m2 m3 t c. (MMonad t, Monad m3) => (forall b. m2 b -> t m3 b)
                                                   -> (forall a. m1 a -> t m2 a)
                                                   ->            m1 c -> t m3 c
(<|<) g f m = embed g (f m)

(=<|) :: forall t m n b. (MMonad t, Monad n) => (forall a. m a -> t n a)
                                             ->          t m b -> t n b
(=<|) = embed

(|>=) :: forall t m n b. (MMonad t, Monad n) => t m b
                                             -> (forall a. m a -> t n a)
                                             -> t n b
(|>=) t f = embed f t

instance mmonadExceptT :: MMonad (E.ExceptT e) where
  embed f m = E.ExceptT (do
                        x <- E.runExceptT (f (E.runExceptT m))
                        return (case x of
                               Left e -> Left e
                               Right (Left e) -> Left e
                               Right (Right a) -> Right a))

--instance mmonadListT :: MMonad L.ListT where
  --embed f m = L.ListT (do
                      --x <- L.runListT (f (L.runListT m))
                      --return (concat x))

instance mmonadMaybeT :: MMonad M.MaybeT where
  embed f m = M.MaybeT (do
                       x <- M.runMaybeT (f (M.runMaybeT m))
                       return (case x of
                              Nothing -> Nothing
                              Just Nothing -> Nothing
                              Just (Just a) -> Just a))

instance mmonadReaderT :: MMonad (R.ReaderT r) where
  embed f m = R.ReaderT (\ i -> R.runReaderT (f (R.runReaderT m i)) i)

instance mmonadWriterT :: (Monoid w) => MMonad (W.WriterT w) where
  embed f m = W.WriterT (do
                        Tuple (Tuple a w1) w2 <- W.runWriterT (f (W.runWriterT m))
                        return (Tuple a (append w1 w2)))
