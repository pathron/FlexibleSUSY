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

#include <cmath>
#include "sum.hpp"

#define BOOST_TEST_DYN_LINK
#define BOOST_TEST_MODULE test_sum

#include <boost/test/unit_test.hpp>
#include <boost/test/floating_point_comparison.hpp>

using namespace std;
using namespace flexiblesusy;

BOOST_AUTO_TEST_CASE(test_sum)
{
    BOOST_CHECK_EQUAL((sum<size_t, 0, 10>([](size_t i){ return i; })), 55);
    BOOST_CHECK_EQUAL((sum<char, -10, 0>([](char i){ return i; })), -55);

    double c = 6;
    BOOST_CHECK_CLOSE_FRACTION(sqrt(SUM(i, 1, 1000, c/i/i)), 3.14, 1e-3);
    BOOST_CHECK_EQUAL(SUM(char, i, -10, 0, i), -55);

    // intended to fail
    BOOST_WARN_EQUAL((sum<unsigned char, -10, 0>([](char i){return i;})), -55);
    BOOST_WARN_EQUAL(SUM(unsigned char, i, -10, 0, i), -55);
}

BOOST_AUTO_TEST_CASE(test_multi_sum)
{
    BOOST_CHECK_EQUAL(SUM(i, 1, 3, SUM(j, 1, 5, (i+7)*j)), 405);
    BOOST_CHECK_EQUAL(SUM(char, i, -4, 0, SUM(int, j, 1, 9, i+j)), 135);
}
