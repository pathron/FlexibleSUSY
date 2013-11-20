// ====================================================================
// This file is part of FlexibleSUSY.
//
// FlexibleSUSY is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published
// by the Free Software Foundation, either version 3 of the License,
// or (at your option) any later version.
//
// FlexibleSUSY is distributed in the hope that it will be useful, but
// WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
// General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with FlexibleSUSY.  If not, see
// <http://www.gnu.org/licenses/>.
// ====================================================================

#define BOOST_TEST_DYN_LINK
#define BOOST_TEST_MODULE test_complex_op_int

#include <complex>
#include <boost/test/unit_test.hpp>
#include "complex_op_int.hpp"

using namespace flexiblesusy;
using namespace std;

BOOST_AUTO_TEST_CASE(test_complex_op_int)
{
    typedef complex<double> Complex;

    BOOST_CHECK_SMALL(abs((Complex(6) + 2) - Complex(8)), 1e-15);
    BOOST_CHECK_SMALL(abs((6 + Complex(2)) - Complex(8)), 1e-15);

    BOOST_CHECK_SMALL(abs((Complex(6) - 2) - Complex(4)), 1e-15);
    BOOST_CHECK_SMALL(abs((6 - Complex(2)) - Complex(4)), 1e-15);

    BOOST_CHECK_SMALL(abs((Complex(3) * 2) - Complex(6)), 1e-15);
    BOOST_CHECK_SMALL(abs((3 * Complex(2)) - Complex(6)), 1e-15);

    BOOST_CHECK_SMALL(abs((Complex(6) / 2) - Complex(3)), 1e-15);
    BOOST_CHECK_SMALL(abs((6 / Complex(2)) - Complex(3)), 1e-15);
}
