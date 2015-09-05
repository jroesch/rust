// The transactional interface for the type checker. Currently we must have duplicate interfaces,
// because some contexts are used via a &T, and sometimes used by &mut T. I would imagine at some
// point we can have a single interface that works purely through &mut T, since most contexts
// require mutability.

pub trait TransactionalMut: Sized {
    type Snapshot;

    fn start_snapshot(&mut self) -> Self::Snapshot;
    fn rollback_to(&mut self, cause: &str, snapshot: Self::Snapshot);
    fn commit_from(&mut self, snapshot: Self::Snapshot);

    /// Execute `f` and commit the bindings
    fn commit_unconditionally<R, F>(&mut self, f: F) -> R where
        F: FnOnce() -> R,
    {
        debug!("commit()");
        let snapshot = self.start_snapshot();
        let r = f();
        self.commit_from(snapshot);
        r
    }

    /// Execute `f` and commit the bindings if closure `f` returns `Ok(_)`
    fn commit_if_ok<T, E, F>(&mut self, f: F) -> Result<T, E> where
        F: FnOnce(&Self::Snapshot, &mut Self) -> Result<T, E>
    {
        debug!("commit_if_ok()");
        let snapshot = self.start_snapshot();
        let r = f(&snapshot, self);
        debug!("commit_if_ok() -- r.is_ok() = {}", r.is_ok());
        match r {
            Ok(_) => { self.commit_from(snapshot); }
            Err(_) => { self.rollback_to("Transactional::commit_if_ok", snapshot); }
        }
        r
    }

    /// Execute `f` then unroll any bindings it creates
    fn probe<R, F>(&mut self, f: F) -> R where
        F: FnOnce(&Self::Snapshot, &mut Self) -> R,
    {
        debug!("probe()");
        let snapshot = self.start_snapshot();
        let r = f(&snapshot, self);
        self.rollback_to("probe", snapshot);
        r
    }
}

pub trait Transactional: Sized {
    type Snapshot;

    fn start_snapshot(&self) -> Self::Snapshot;
    fn rollback_to(&self, cause: &str, snapshot: Self::Snapshot);
    fn commit_from(&self, snapshot: Self::Snapshot);

    /// Execute `f` and commit the bindings
    fn commit_unconditionally<R, F>(&self, f: F) -> R where
        F: FnOnce() -> R,
    {
        debug!("commit()");
        let snapshot = self.start_snapshot();
        let r = f();
        self.commit_from(snapshot);
        r
    }

    /// Execute `f` and commit the bindings if closure `f` returns `Ok(_)`
    fn commit_if_ok<T, E, F>(&self, f: F) -> Result<T, E> where
        F: FnOnce(&Self::Snapshot, &Self) -> Result<T, E>
    {
        debug!("commit_if_ok()");
        let snapshot = self.start_snapshot();
        let r = f(&snapshot, self);
        debug!("commit_if_ok() -- r.is_ok() = {}", r.is_ok());
        match r {
            Ok(_) => { self.commit_from(snapshot); }
            Err(_) => { self.rollback_to("Transactional::commit_if_ok", snapshot); }
        }
        r
    }

    /// Execute `f` then unroll any bindings it creates
    fn probe<R, F>(&self, f: F) -> R where
        F: FnOnce(&Self::Snapshot, &Self) -> R,
    {
        debug!("probe()");
        let snapshot = self.start_snapshot();
        let r = f(&snapshot, self);
        self.rollback_to("probe", snapshot);
        r
    }
}
