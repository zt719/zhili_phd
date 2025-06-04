module HFunc where

type f :~> g = forall a. f a -> g a

(|.|) :: g :~> h -> f :~> g -> f :~> h
(|.|) alpha beta fa = alpha (beta fa)

class HFunctor h where
  hmap :: f :~> g -> h f :~> h g
  {- forall a. hmap id a == id a -}
  {- forall a. hmap (f |.| g) a == (hmap f |.| hmap g) a -}

class HFunctor h => HApplicative h where
  hpure :: f :~> h f
--  hap   :: h (f :~> g) -> h f :~> h g

class HApplicative m => HMonad m where
  hreturn :: f :~> m f
  hreturn = hpure
  
  (>=>)   :: g :~> m h -> f :~> m g -> f :~> m h

newtype App f a = App { unApp :: f a }

instance HFunctor App where
  hmap alpha (App fa) = App (alpha fa)

instance HApplicative App where
  hpure = App

instance HMonad App where
  (g2mh >=> f2mg) fa = g2mh (unApp (f2mg fa))
