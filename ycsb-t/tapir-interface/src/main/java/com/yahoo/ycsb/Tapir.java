package com.yahoo.ycsb;

import org.bytedeco.javacpp.*;
import org.bytedeco.javacpp.annotation.*;

@Platform(include={"../../store/tapirstore/client.h"})
@Namespace("tapirstore")

public class Tapir {

   public static class Client extends Pointer {
      static { Loader.load(); }
      public Client(String configPath, int nshards, int closestReplica) { allocate(configPath, nshards, closestReplica); }
      private native void allocate(@StdString String configPath, int nshards, int closestReplica);

      // to call the getter and setter functions
      public native void Begin();
      public native @StdString String Get(@StdString String key);
      public native int Put(@StdString String key, @StdString String value);
      public native @Cast("bool") boolean Commit();
      public native void Abort();
   }
}
