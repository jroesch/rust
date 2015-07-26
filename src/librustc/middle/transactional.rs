pub trait Transactional: Sized {
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
