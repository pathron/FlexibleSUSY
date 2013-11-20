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

#include <complex>

#ifndef complex_op_int_hpp
#define complex_op_int_hpp

namespace flexiblesusy {

inline
std::complex<double> operator+(const std::complex<double>& z, const double x)
{
    return z + std::complex<double>(x);
}

inline
std::complex<double> operator+(const double x, const std::complex<double>& z)
{
    return std::complex<double>(x) + z;
}

inline
std::complex<double> operator-(const std::complex<double>& z, const double x)
{
    return z - std::complex<double>(x);
}

inline
std::complex<double> operator-(const double x, const std::complex<double>& z)
{
    return std::complex<double>(x) - z;
}

inline
std::complex<double> operator*(const std::complex<double>& z, const double x)
{
    return z * std::complex<double>(x);
}

inline
std::complex<double> operator*(const double x, const std::complex<double>& z)
{
    return std::complex<double>(x) * z;
}

inline
std::complex<double> operator/(const std::complex<double>& z, const double x)
{
    return z / std::complex<double>(x);
}

inline
std::complex<double> operator/(const double x, const std::complex<double>& z)
{
    return std::complex<double>(x) / z;
}

} // namespace flexiblesusy

#endif
