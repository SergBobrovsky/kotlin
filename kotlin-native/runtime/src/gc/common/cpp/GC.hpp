/*
 * Copyright 2010-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license
 * that can be found in the LICENSE file.
 */

#pragma once

#include "GCScheduler.hpp"
#include "Types.h"

namespace kotlin {

namespace mm {
class ThreadData;
}

namespace gc {

class GC {
public:
    class ThreadData {
    public:
        virtual ~ThreadData() = default;

        virtual ObjHeader* CreateObject(const TypeInfo* typeInfo) noexcept = 0;
        virtual ArrayHeader* CreateArray(const TypeInfo* typeInfo, uint32_t elements) noexcept = 0;

        virtual void Publish() noexcept = 0;
        virtual void ClearForTests() noexcept = 0;

        virtual void PerformFullGC() noexcept = 0;
        // TODO: No, remove it from here.
        virtual void OnStoppedForGC() noexcept = 0;
    };

    virtual ~GC() = default;

    virtual void ClearForTests() noexcept = 0;

    virtual KStdUniquePtr<ThreadData> CreateThreadData(mm::ThreadData&) noexcept = 0;
    virtual GCSchedulerConfig& GCSchedulerConfig() noexcept = 0;
};

KStdUniquePtr<GC> CreateGC() noexcept;

void SafePointFunctionPrologue(gc::GC::ThreadData& threadData) noexcept;
void SafePointLoopBody(gc::GC::ThreadData& threadData) noexcept;

} // namespace gc
} // namespace kotlin
