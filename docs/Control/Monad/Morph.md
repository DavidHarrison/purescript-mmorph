## Module Control.Monad.Morph

A port of Haskell's [mmorph library](http://hackage.haskell.org/package/mmorph-1.0.0/docs/Control-Monad-Morph.html)

#### `MInvariant`

``` purescript
class MInvariant t where
  ihoist :: forall m n. (Monad m, Monad n) => Natural m n -> Natural n m -> Natural (t m) (t n)
```

##### Instances
``` purescript
instance minvariantContT :: MInvariant (ContT r)
instance minvariantExceptT :: MInvariant (ExceptT e)
instance minvariantMaybeT :: MInvariant MaybeT
instance minvariantReaderT :: MInvariant (ReaderT r)
instance minvariantWriterT :: MInvariant (WriterT w)
instance minvariantStateT :: MInvariant (StateT s)
instance minvariantRWST :: MInvariant (RWST r w s)
instance minvariantCompose :: (Functor f) => MInvariant (Compose f)
instance minvariantProduct :: MInvariant (Product f)
instance minvariantCoproduct :: MInvariant (Coproduct f)
instance minvariantFreeT :: (Functor f) => MInvariant (FreeT f)
```

#### `ihoistF`

``` purescript
ihoistF :: forall t m n. (MFunctor t, Monad m) => Natural m n -> Natural n m -> Natural (t m) (t n)
```

#### `MFunctor`

``` purescript
class MFunctor t where
  hoist :: forall m n. (Monad m) => Natural m n -> Natural (t m) (t n)
```

##### Instances
``` purescript
instance mfunctorExceptT :: MFunctor (ExceptT e)
instance mfunctorMaybeT :: MFunctor MaybeT
instance mfunctorReaderT :: MFunctor (ReaderT r)
instance mfunctorWriterT :: MFunctor (WriterT w)
instance mfunctorStateT :: MFunctor (StateT s)
instance mfunctorRWST :: MFunctor (RWST r w s)
instance mfunctorCompose :: (Functor f) => MFunctor (Compose f)
instance mfunctorProduct :: MFunctor (Product f)
instance mfunctorCoproduct :: MFunctor (Coproduct f)
```

#### `generalize`

``` purescript
generalize :: forall m a. (Monad m) => Identity a -> m a
```

#### `MMonad`

``` purescript
class (MFunctor t, MonadTrans t) <= MMonad t where
  embed :: forall n m b. (Monad n) => (forall a. m a -> t n a) -> t m b -> t n b
```

##### Instances
``` purescript
instance mmonadExceptT :: MMonad (ExceptT e)
instance mmonadMaybeT :: MMonad MaybeT
instance mmonadReaderT :: MMonad (ReaderT r)
instance mmonadWriterT :: (Monoid w) => MMonad (WriterT w)
```

#### `squash`

``` purescript
squash :: forall a m t. (Monad m, MMonad t) => t (t m) a -> t m a
```

#### `(>|>)`

``` purescript
(>|>) :: forall m1 m2 m3 t c. (MMonad t, Monad m3) => (forall a. m1 a -> t m2 a) -> (forall b. m2 b -> t m3 b) -> m1 c -> t m3 c
```

_right-associative / precedence 2_

#### `(<|<)`

``` purescript
(<|<) :: forall m1 m2 m3 t c. (MMonad t, Monad m3) => (forall b. m2 b -> t m3 b) -> (forall a. m1 a -> t m2 a) -> m1 c -> t m3 c
```

_left-associative / precedence 2_

#### `(=<|)`

``` purescript
(=<|) :: forall t m n b. (MMonad t, Monad n) => (forall a. m a -> t n a) -> t m b -> t n b
```

_right-associative / precedence 2_

#### `(|>=)`

``` purescript
(|>=) :: forall t m n b. (MMonad t, Monad n) => t m b -> (forall a. m a -> t n a) -> t n b
```

_left-associative / precedence 2_


