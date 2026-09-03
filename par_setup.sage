import os, multiprocessing
import sys, resource, ctypes, signal

if os.environ.get('SAGE_NUM_THREADS', '1') == '1':
    try:
        ncpu = N_CPU            # use N_CPU parameter if it's defined
    except NameError:
        ncpu = multiprocessing.cpu_count()
    sys.stderr.write(f'WARNING: setting SAGE_NUM_THREADS = {ncpu}.\n')
    os.environ['SAGE_NUM_THREADS'] = str(ncpu)

'''
Fix for errors like:
    signal: sage-eval[2291411] overflowed sigaltstack
    Pid 2291371(sage-eval) over core_pipe_limit
'''

# Increase recursion depth (safe)
sys.setrecursionlimit(20000)            # default is 3000

# Increase thread stack size
soft, hard = resource.getrlimit(resource.RLIMIT_STACK)
resource.setrlimit(resource.RLIMIT_STACK, (64 * 1024 * 1024, hard))

# Increase alternate signal stack size
SIGSTKSZ = 256 * 1024  # 256 KB

# allocate memory safely
try:
    stack = ctypes.create_string_buffer(SIGSTKSZ)
except TypeError:
    stack = ctypes.create_string_buffer(b"\x00" * SIGSTKSZ)

libc = ctypes.CDLL(None)
stack_ptr = ctypes.c_void_p(ctypes.addressof(stack))

# struct sigaltstack { void *ss_sp; int ss_flags; size_t ss_size; }
# We'll set ss_flags = 0 (enable)
class stack_t(ctypes.Structure):
    _fields_ = [("ss_sp", ctypes.c_void_p),
                ("ss_flags", ctypes.c_int),
                ("ss_size", ctypes.c_size_t)]

ss = stack_t(stack_ptr, 0, SIGSTKSZ)

# call sigaltstack
libc.sigaltstack(ctypes.byref(ss), None)
