/*
 * Copyright 2010-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license
 * that can be found in the LICENSE file.
 */

#include "GCImpl.hpp"

#include "GC.hpp"
#include "GCScheduler.hpp"
#include "ObjectFactory.hpp"
#include "SameThreadMarkAndSweep.hpp"

using namespace kotlin;

namespace {

class GCImpl;

class GCThreadDataImpl : public gc::GC::ThreadData {
public:
    static GCThreadDataImpl& From(gc::GC::ThreadData& threadData) noexcept { return static_cast<GCThreadDataImpl&>(threadData); }

    GCThreadDataImpl(GCImpl& gc, mm::ThreadData& threadData) noexcept;

    gc::SameThreadMarkAndSweep::ThreadData& gc() noexcept { return gc_; }
    gc::ObjectFactory<gc::SameThreadMarkAndSweep>::ThreadQueue& objectFactoryThreadQueue() noexcept { return objectFactoryThreadQueue_; }

    ObjHeader* CreateObject(const TypeInfo* typeInfo) noexcept override { return objectFactoryThreadQueue_.CreateObject(typeInfo); }

    ArrayHeader* CreateArray(const TypeInfo* typeInfo, uint32_t elements) noexcept override {
        return objectFactoryThreadQueue_.CreateArray(typeInfo, elements);
    }

    void Publish() noexcept override { objectFactoryThreadQueue_.Publish(); }

    void ClearForTests() noexcept override { objectFactoryThreadQueue_.ClearForTests(); }

    void PerformFullGC() noexcept override { gc_.PerformFullGC(); }

    void OnStoppedForGC() noexcept override { gcScheduler_.OnStoppedForGC(); }

private:
    gc::GCSchedulerThreadData gcScheduler_;
    gc::SameThreadMarkAndSweep::ThreadData gc_;
    gc::ObjectFactory<gc::SameThreadMarkAndSweep>::ThreadQueue objectFactoryThreadQueue_;
};

class GCImpl : public gc::GC {
public:
    static GCImpl& From(gc::GC& gc) noexcept { return static_cast<GCImpl&>(gc); }

    GCImpl() noexcept : gc_(objectFactory_, gcScheduler_) {}

    void ClearForTests() noexcept override { objectFactory_.ClearForTests(); }

    KStdUniquePtr<gc::GC::ThreadData> CreateThreadData(mm::ThreadData& threadData) noexcept override {
        return make_unique<GCThreadDataImpl>(*this, threadData);
    }

    gc::GCSchedulerConfig& GCSchedulerConfig() noexcept override { return gcScheduler_.config(); }

    gc::ObjectFactory<gc::SameThreadMarkAndSweep>& objectFactory() noexcept { return objectFactory_; }
    gc::GCScheduler& gcScheduler() noexcept { return gcScheduler_; }
    gc::SameThreadMarkAndSweep& gc() noexcept { return gc_; }

private:
    gc::ObjectFactory<gc::SameThreadMarkAndSweep> objectFactory_;
    gc::GCScheduler gcScheduler_;
    gc::SameThreadMarkAndSweep gc_;
};

GCThreadDataImpl::GCThreadDataImpl(GCImpl& gc, mm::ThreadData& threadData) noexcept :
    gcScheduler_(gc.gcScheduler().NewThreadData()),
    gc_(gc.gc(), threadData, gcScheduler_),
    objectFactoryThreadQueue_(gc.objectFactory(), gc_) {}

} // namespace

KStdUniquePtr<gc::GC> gc::CreateGC() noexcept {
    return make_unique<GCImpl>();
}

void gc::SafePointFunctionPrologue(gc::GC::ThreadData& threadData) noexcept {
    auto& threadDataImpl = GCThreadDataImpl::From(threadData);
    threadDataImpl.gc().SafePointFunctionPrologue();
}

void gc::SafePointLoopBody(gc::GC::ThreadData& threadData) noexcept {
    auto& threadDataImpl = GCThreadDataImpl::From(threadData);
    threadDataImpl.gc().SafePointLoopBody();
}

gc::ObjectFactory<gc::SameThreadMarkAndSweep>& gc::GetObjectFactory(gc::GC& gc) noexcept {
    auto& gcImpl = GCImpl::From(gc);
    return gcImpl.objectFactory();
}

gc::ObjectFactory<gc::SameThreadMarkAndSweep>::ThreadQueue& gc::GetObjectFactoryThreadQueue(gc::GC::ThreadData& threadData) noexcept {
    auto& threadDataImpl = GCThreadDataImpl::From(threadData);
    return threadDataImpl.objectFactoryThreadQueue();
}

gc::GCScheduler& gc::GetGCScheduler(gc::GC& gc) noexcept {
    auto& gcImpl = GCImpl::From(gc);
    return gcImpl.gcScheduler();
}
