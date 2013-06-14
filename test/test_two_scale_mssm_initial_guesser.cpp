#include "mssm_parameter_point.hpp"
#include "mssm_two_scale.hpp"
#include "mssm_two_scale_initial_guesser.hpp"
#include "softsusy.h"
#include "logger.hpp"
#include "stopwatch.hpp"
#include "test.h"

#define BOOST_TEST_DYN_LINK
#define BOOST_TEST_MODULE test_two_scale_mssm_initial_guesser

#include <boost/test/unit_test.hpp>

/**
 * This function is a copy of the initial guess part that Softsusy
 * runs before the iteration starts.
 *
 * @param mssm model class
 * @param pp parameter point
 */
double softsusy_initial_guess(MssmSoftsusy& mssm, const Mssm_parameter_point& pp)
{
   double mx = 0.0;
   const double mxGuess = pp.mxGuess;
   const double tanb = pp.tanBeta;
   const DoubleVector& pars = pp.get_soft_pars();
   const int sgnMu = pp.signMu;
   const bool ewsbBCscale = false;
   typedef void (*TBoundaryCondition)(MssmSoftsusy&, const DoubleVector&);
   TBoundaryCondition boundaryCondition = sugraBcs;

   const static MssmSoftsusy empty;

   double muFirst = mssm.displaySusyMu(); /// Remember initial values
   bool setTbAtMXflag = mssm.displaySetTbAtMX();
   bool altFlag = mssm.displayAltEwsb();
   double m32 = mssm.displayGravitino();
   double muCondFirst = mssm.displayMuCond();
   double maCondFirst = mssm.displayMaCond();
   const QedQcd& oneset = pp.oneset;

   mssm.setSoftsusy(empty); /// Always starts from an empty object
   /// These are things that are re-written by the new initialisation
   mssm.setSetTbAtMX(setTbAtMXflag);
   if (altFlag) mssm.useAlternativeEwsb();
   mssm.setData(oneset);
   mssm.setMw(MW);
   mssm.setM32(m32);
   mssm.setMuCond(muCondFirst);
   mssm.setMaCond(maCondFirst);

   double mz = mssm.displayMz();

   /// Here all was same
   if (mxGuess > 0.0)
      mx = mxGuess;
   else {
      string ii("Trying to use negative mx in MssmSoftsusy::lowOrg.\n");
      ii = ii + "Now illegal! Use positive mx for first guess of mx.\n";
      throw ii;
   }

   if (oneset.displayMu() != mz) {
      cout << "WARNING: lowOrg in softsusy.cpp called with oneset at scale\n"
	   << oneset.displayMu() << "\ninstead of " << mz << endl;
   }

   MssmSusy t(mssm.guessAtSusyMt(tanb, oneset));

   t.setLoops(2); /// 2 loops should protect against ht Landau pole
   t.runto(mx);

   mssm.setSusy(t);

   /// Initial guess: B=0, mu=1st parameter, need better guesses
   boundaryCondition(mssm, pars);

   if ((sgnMu == 1 || sgnMu == -1) && !ewsbBCscale) {
      mssm.setSusyMu(sgnMu * 1.0);
      mssm.setM3Squared(0.);
   }
   else {
      if (mssm.displayAltEwsb()) {
         mssm.setSusyMu(mssm.displayMuCond());
         mssm.setM3Squared(mssm.displayMaCond());
      }
      else {
         mssm.setSusyMu(muFirst);
         mssm.setM3Squared(muFirst);
      }
   }

   mssm.run(mx, mz);

   if (sgnMu == 1 || sgnMu == -1)
      mssm.rewsbTreeLevel(sgnMu);

   mssm.physical(0);
   mssm.setThresholds(3);
   mssm.setLoops(2);

   return mx;
}

void test_equality(const SoftParsMssm& a, const SoftParsMssm& b)
{
   BOOST_CHECK_EQUAL(a.displayLoops()     , b.displayLoops());
   BOOST_CHECK_EQUAL(a.displayMu()        , b.displayMu());
   BOOST_CHECK_EQUAL(a.displayThresholds(), b.displayThresholds());

   BOOST_CHECK_CLOSE(a.displayGaugeCoupling(1), b.displayGaugeCoupling(1), 1.0e-5);
   BOOST_CHECK_CLOSE(a.displayGaugeCoupling(2), b.displayGaugeCoupling(2), 1.0e-5);
   BOOST_CHECK_CLOSE(a.displayGaugeCoupling(3), b.displayGaugeCoupling(3), 1.0e-5);

   TEST_CLOSE(a.displayYukawaMatrix(YU), b.displayYukawaMatrix(YU), 1.0e-5);
   TEST_CLOSE(a.displayYukawaMatrix(YD), b.displayYukawaMatrix(YD), 1.0e-5);
   TEST_CLOSE(a.displayYukawaMatrix(YE), b.displayYukawaMatrix(YE), 1.0e-5);

   BOOST_CHECK_CLOSE(a.displayGaugino(1), b.displayGaugino(1), 1.0e-5);
   BOOST_CHECK_CLOSE(a.displayGaugino(2), b.displayGaugino(2), 1.0e-5);
   BOOST_CHECK_CLOSE(a.displayGaugino(3), b.displayGaugino(3), 1.0e-5);

   BOOST_CHECK_CLOSE(a.displayMh1Squared(), b.displayMh1Squared(), 1.0e-5);
   BOOST_CHECK_CLOSE(a.displayMh2Squared(), b.displayMh2Squared(), 1.0e-5);

   TEST_CLOSE(a.displaySoftMassSquared(mQl), b.displaySoftMassSquared(mQl), 1.0e-5);
   TEST_CLOSE(a.displaySoftMassSquared(mUr), b.displaySoftMassSquared(mUr), 1.0e-5);
   TEST_CLOSE(a.displaySoftMassSquared(mDr), b.displaySoftMassSquared(mDr), 1.0e-5);
   TEST_CLOSE(a.displaySoftMassSquared(mLl), b.displaySoftMassSquared(mLl), 1.0e-5);
   TEST_CLOSE(a.displaySoftMassSquared(mEr), b.displaySoftMassSquared(mEr), 1.0e-5);

   TEST_CLOSE(a.displayTrilinear(UA), b.displayTrilinear(UA), 1.0e-5);
   TEST_CLOSE(a.displayTrilinear(DA), b.displayTrilinear(DA), 1.0e-5);
   TEST_CLOSE(a.displayTrilinear(EA), b.displayTrilinear(EA), 1.0e-5);

   BOOST_CHECK_CLOSE(a.displaySusyMu(), b.displaySusyMu(), 1.0e-5);
   BOOST_CHECK_CLOSE(a.displayM3Squared(), b.displayM3Squared(), 1.0e-5);

   BOOST_CHECK_CLOSE(a.displayTanb(), b.displayTanb(), 1.0e-5);
   BOOST_CHECK_CLOSE(a.displayHvev(), b.displayHvev(), 1.0e-5);
}

BOOST_AUTO_TEST_CASE( test_softsusy_mssm_initial_guesser )
{
   Mssm_parameter_point pp;
   pp.tanBeta = 45.1;
   Mssm<Two_scale> mssm;
   Mssm_initial_guesser initial_guesser(&mssm, pp.oneset, pp.mxGuess, pp.tanBeta, pp.signMu, pp.get_soft_pars(), false);

   initial_guesser.guess();

   MssmSoftsusy softsusy;
   softsusy_initial_guess(softsusy, pp);

   test_equality(mssm, softsusy);
}