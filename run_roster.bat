@echo off

REM ============================================================
REM ROSTER PERIOD
REM ============================================================

set START=26/10/2026
set END=03/01/2027


REM ============================================================
REM INPUT FILES
REM ============================================================

set ASSIGNED=assignedOctJan.txt
set LEAVE=octjan_leave.txt


REM ============================================================
REM OUTPUT FILES
REM ============================================================

set PIVOT=octjan_pivot.csv
set ROSTER=octjan_roster.mzn
set LEAVEOUT=octjan_leave.mzn


REM ============================================================
REM STAGE 1: OPTIMA -> PIVOT
REM ============================================================

echo.
echo Creating %PIVOT% ...

gawk -v start=%START% -v end=%END% -f pivot2.txt %ASSIGNED% > %PIVOT%

if errorlevel 1 (
    echo ERROR running pivot2.txt
    pause
    exit /b 1
)


REM ============================================================
REM STAGE 2: PIVOT -> MINIZINC
REM ============================================================

echo Creating %ROSTER% ...

gawk -f roster_to_SICmzn.txt %PIVOT% > %ROSTER%

if errorlevel 1 (
    echo ERROR running roster_to_SICmzn.txt
    pause
    exit /b 1
)


REM ============================================================
REM LEAVE -> MINIZINC
REM ============================================================

echo Creating %LEAVEOUT% ...

gawk -v start=%START% -v end=%END% -f leave_to_mzn.txt %LEAVE% > %LEAVEOUT%

if errorlevel 1 (
    echo ERROR running leave_to_mzn.txt
    pause
    exit /b 1
)


REM ============================================================
REM FINISHED
REM ============================================================

echo.
echo ========================================
echo ROSTER BUILD COMPLETE
echo ========================================
echo.
echo Created:
echo   %PIVOT%
echo   %ROSTER%
echo   %LEAVEOUT%
echo.

pause