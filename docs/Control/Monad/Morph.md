## Module Control.Monad.Morph

A port of Haskell's [mmorph library](http://hackage.haskell.org/package/mmorph-1.0.0/docs/Control-Monad-Morph.html)

#### `MInvariant`

``` purescript
class MInvariant t where
  ihoist :: forall m n. (Monad m, Monad n) => Natural m n -> Natural n m -> Natural (t m) (t n)
```

A `MInvariant` is an invariant functor in the category of monads,
using `ihoist` as the analog of
[`imap`](http://pursuit.purescript.org/packages/purescript-invariant/0.3.0/docs/Data.Functor.Invariant#v:imap).

Instances must satisfy the following laws:

- Identity: `ihoist id id = id`
- Composition: `ihoist g1 g2 <<< ihoist f1 f2 = ihoist (g1 <<< f1) (f2 <<< g2)`


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

As all `MFunctor`s are also trivially `MInvariant`, this function can be
used as the `ihoist` implementation for all `MInvariant` instances for
`MFunctors`.

#### `MFunctor`

``` purescript
class MFunctor t where
  hoist :: forall m n. (Monad m) => Natural m n -> Natural (t m) (t n)
```

A `MFunctor` is a functor in the category of monads,
using `hoist` as the analog of `map`.

Instances must satisfy the following laws:

- Identity: `hoist id = id`
- Composition: `hoist (f <<< g) = hoist f <<< hoist g`


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
generalize :: forall m. (Monad m) => Natural Identity m
```

#### `MMonad`

``` purescript
class (MFunctor t, MonadTrans t) <= MMonad t where
  embed :: forall n m. (Monad n) => Natural m (t n) -> Natural (t m) (t n)
```

A `MMonad` is a functor in the category of monads,
using `embed` as the analog of `bind`.

Instances must satisfy the following laws in addition to the
`MFunctor` and `MonadTrans` laws:

- TODO: Associative composition: `(hoist (<<<) f) <*> g <*> h = f <*> (g <*> h)`
- Associativity: `embed g (embed f x) = embed (\k -> embed g (f k)) x`
- Left Identity: `embed f (lift x) = f x`
- Right Identity: `embed lift x = x`


##### Instances
``` purescript
instance mmonadExceptT :: MMonad (ExceptT e)
instance mmonadMaybeT :: MMonad MaybeT
instance mmonadReaderT :: MMonad (ReaderT r)
instance mmonadWriterT :: (Monoid w) => MMonad (WriterT w)
```

#### `squash`

``` purescript
squash :: forall m t. (Monad m, MMonad t) => Natural (t (t m)) (t m)
```

#### `(>|>)`

``` purescript
(>|>) :: forall m1 m2 m3 t. (MMonad t, Monad m3) => Natural m1 (t m2) -> Natural m2 (t m3) -> Natural m1 (t m3)
```

_right-associative / precedence 2_

#### `(<|<)`

``` purescript
(<|<) :: forall m1 m2 m3 t. (MMonad t, Monad m3) => Natural m2 (t m3) -> Natural m1 (t m2) -> Natural m1 (t m3)
```

_left-associative / precedence 2_

#### `(=<|)`

``` purescript
(=<|) :: forall t m n. (MMonad t, Monad n) => Natural m (t n) -> Natural (t m) (t n)
```

_right-associative / precedence 2_

#### `(|>=)`

``` purescript
(|>=) :: forall t m n b. (MMonad t, Monad n) => t m b -> Natural m (t n) -> t n b
```

_left-associative / precedence 2_


