/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    timeout.cpp

Abstract:

    Timeout support

Author:

    Leonardo de Moura (leonardo) 2006-10-02.

Revision History:

    Christoph (cwinter) 2012-02-14: Switch to scoped_timer for timeout support on all platforms.

--*/
#include<iostream>
#include"z3_omp.h"
#include"util.h"
#include"timeout.h"
#include"error_codes.h"

#include"event_handler.h"
#include"scoped_timer.h"
#include"stopwatch.h"

scoped_timer * g_timeout = 0;
void (* g_on_timeout)() = 0;

class g_timeout_eh : public event_handler {
public:
    void operator()() {
        #pragma omp critical (g_timeout_cs) 
        {
            std::cout << "timeout\n";
            if (g_on_timeout)
                g_on_timeout();
            if (g_timeout) 
                delete g_timeout;
            g_timeout = 0;
            throw z3_error(ERR_TIMEOUT);
        }
    }
};

void set_timeout(long ms) {
    if (g_timeout) 
        delete g_timeout;

    g_timeout = new scoped_timer(ms, new g_timeout_eh());
}

void register_on_timeout_proc(void (*proc)()) {
    g_on_timeout = proc;
}

#if defined(_WINDOWS) || defined(_CYGWIN)

static double get_user_cpu_seconds()
{
    FILETIME createTime;
    FILETIME exitTime;
    FILETIME kernelTime;
    FILETIME userTime;

    GetProcessTimes(GetCurrentProcess(), &createTime, &exitTime, &kernelTime, &userTime);
    SYSTEMTIME userSystemTime;
    FileTimeToSystemTime(&userTime,&userSystemTime );
    return (double)userSystemTime.wHour * 3600.0 +
        (double)userSystemTime.wMinute * 60.0 +
        (double)userSystemTime.wSecond +
        (double)userSystemTime.wMilliseconds / 1000.0;
}

#else

static double get_user_cpu_seconds()
{
    return 0.0;
}
#endif

 class g_user_cpu_timeout_eh : public g_timeout_eh {
      double m_secs;
public:
    g_user_cpu_timeout_eh(int ms){
        m_secs = 0.001 * ms;
    }
    void operator()() {
        #pragma omp critical (g_timeout_cs) 
        {
            double csecs = get_user_cpu_seconds();
            //            std::cout << "limit: " << m_secs << ", current: " << csecs << "\n";
            if (csecs > m_secs)
                g_timeout_eh::operator()();
        }
    }
};


void set_user_cpu_timeout(long ms) {
    if (g_timeout) 
        delete g_timeout;

    g_timeout = new scoped_timer(1000, new g_user_cpu_timeout_eh(ms));
}
