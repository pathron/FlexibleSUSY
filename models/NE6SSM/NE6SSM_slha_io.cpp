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

// File generated at Tue 8 Jul 2014 14:47:11

#include "NE6SSM_slha_io.hpp"
#include "NE6SSM_input_parameters.hpp"
#include "logger.hpp"
#include "wrappers.hpp"
#include "numerics.hpp"
#include "spectrum_generator_settings.hpp"
#include "lowe.h"
#include "config.h"

#include <fstream>
#include <sstream>
#include <iostream>
#include <boost/bind.hpp>

using namespace softsusy;

namespace flexiblesusy {

char const * const NE6SSM_slha_io::drbar_blocks[NUMBER_OF_DRBAR_BLOCKS] =
   { "gauge", "Yu", "Yd", "Ye", "Te", "Td", "Tu", "HMIX", "ESIXHEYUK",
   "ESIXRUN", "ESIXGDYUK", "ESIXFUYUK", "ESIXFDYUK", "ESIXTHETRI", "ESIXTGDTRI"
   , "ESIXTFUTRI", "ESIXTFDTRI", "MSQ2", "MSE2", "MSL2", "MSU2", "MSD2",
   "MSOFT", "mX2", "mXBar2", "ESIXKAPPA", "ESIXTKAPPA", "ESIXLAMBDA",
   "ESIXTLAMBDA" }
;

NE6SSM_slha_io::NE6SSM_slha_io()
   : slha_io()
{
}

void NE6SSM_slha_io::clear()
{
   slha_io.clear();
}

void NE6SSM_slha_io::set_extpar(const NE6SSM_input_parameters& input)
{
   std::ostringstream extpar;

   extpar << "Block EXTPAR\n";
   extpar << FORMAT_ELEMENT(65, input.vSInput, "vSInput");
   extpar << FORMAT_ELEMENT(63, input.muPrimeInput, "muPrimeInput");
   extpar << FORMAT_ELEMENT(64, input.BmuPrimeInput, "BmuPrimeInput");
   extpar << FORMAT_ELEMENT(72, input.QS, "QS");
   slha_io.set_block(extpar);

}

void NE6SSM_slha_io::set_minpar(const NE6SSM_input_parameters& input)
{
   std::ostringstream minpar;

   minpar << "Block MINPAR\n";
   minpar << FORMAT_ELEMENT(3, input.TanBeta, "TanBeta");
   slha_io.set_block(minpar);

}

void NE6SSM_slha_io::set_sminputs(const softsusy::QedQcd& qedqcd)
{
   slha_io.set_sminputs(qedqcd);
}

void NE6SSM_slha_io::set_spinfo(const Problems<NE6SSM_info::NUMBER_OF_PARTICLES>& problems)
{
   std::ostringstream spinfo;
   spinfo << "# FlexibleSUSY " FLEXIBLESUSY_VERSION " SLHA compliant output\n"
             "# P. Athron, Jae-hyeon Park, D. Stöckinger, A. Voigt\n"
             "Block SPINFO\n"
          << FORMAT_SPINFO(1, PKGNAME)
          << FORMAT_SPINFO(2, FLEXIBLESUSY_VERSION);

   if (problems.have_serious_problem()) {
      std::ostringstream serious_problems;
      problems.print(serious_problems);
      spinfo << FORMAT_SPINFO(4, serious_problems.str());
   }

   slha_io.set_block(spinfo, SLHA_io::front);
}

void NE6SSM_slha_io::write_to_file(const std::string& file_name)
{
   slha_io.write_to_file(file_name);
}

double NE6SSM_slha_io::get_input_scale() const
{
   return slha_io.get_extpar().input_scale;
}

double NE6SSM_slha_io::get_parameter_output_scale() const
{
   return slha_io.get_modsel().parameter_output_scale;
}

void NE6SSM_slha_io::read_from_file(const std::string& file_name)
{
   slha_io.read_from_file(file_name);
   slha_io.read_modsel();
   slha_io.read_extpar();
}

void NE6SSM_slha_io::fill(NE6SSM_input_parameters& input) const
{
   SLHA_io::Tuple_processor minpar_processor
      = boost::bind(&NE6SSM_slha_io::fill_minpar_tuple, boost::ref(input), _1, _2);
   SLHA_io::Tuple_processor extpar_processor
      = boost::bind(&NE6SSM_slha_io::fill_extpar_tuple, boost::ref(input), _1, _2);

   slha_io.read_block("MINPAR", minpar_processor);
   slha_io.read_block("EXTPAR", extpar_processor);

   input.g1pInput = slha_io.read_entry("gaugeIN", 4);
   slha_io.read_block("TeIN", input.TYeInput);
   slha_io.read_block("TdIN", input.TYdInput);
   slha_io.read_block("TuIN", input.TYuInput);
   input.XiFInput = slha_io.read_entry("HMIXIN", 30);
   input.MuPhiInput = slha_io.read_entry("HMIXIN", 31);
   input.KappaPrInput = slha_io.read_entry("HMIXIN", 32);
   input.SigmaxInput = slha_io.read_entry("HMIXIN", 33);
   slha_io.read_block("ESIXHEYUKIN", input.hEInput);
   input.SigmaLInput = slha_io.read_entry("ESIXRUNIN", 42);
   slha_io.read_block("ESIXGDYUKIN", input.gDInput);
   slha_io.read_block("ESIXFUYUKIN", input.fuInput);
   slha_io.read_block("ESIXFDYUKIN", input.fdInput);
   input.TKappaPrInput = slha_io.read_entry("ESIXRUNIN", 28);
   input.TSigmaxInput = slha_io.read_entry("ESIXRUNIN", 29);
   slha_io.read_block("ESIXTHETRIIN", input.ThEInput);
   input.TSigmaLInput = slha_io.read_entry("ESIXRUNIN", 43);
   slha_io.read_block("ESIXTGDTRIIN", input.TgDInput);
   slha_io.read_block("ESIXTFUTRIIN", input.TfuInput);
   slha_io.read_block("ESIXTFDTRIIN", input.TfdInput);
   input.BMuPhiInput = slha_io.read_entry("ESIXRUNIN", 30);
   input.LXiFInput = slha_io.read_entry("HMIXIN", 34);
   slha_io.read_block("MSQ2IN", input.mq2Input);
   slha_io.read_block("MSE2IN", input.me2Input);
   slha_io.read_block("MSL2IN", input.ml2Input);
   slha_io.read_block("MSU2IN", input.mu2Input);
   slha_io.read_block("MSD2IN", input.md2Input);
   slha_io.read_block("mX2IN", input.mDx2Input);
   slha_io.read_block("mXBar2IN", input.mDxbar2Input);
   input.mHp2Input = slha_io.read_entry("MSOFTIN", 26);
   input.mHpbar2Input = slha_io.read_entry("MSOFTIN", 27);
   input.MassBInput = slha_io.read_entry("MSOFTIN", 1);
   input.MassWBInput = slha_io.read_entry("MSOFTIN", 2);
   input.MassGInput = slha_io.read_entry("MSOFTIN", 3);
   input.MassBpInput = slha_io.read_entry("MSOFTIN", 4);
   input.vsbInput = slha_io.read_entry("ESIXRUNIN", 12);
   input.vphiInput = slha_io.read_entry("ESIXRUNIN", 13);
   slha_io.read_block("ESIXKAPPAIN", input.KappaInput);
   slha_io.read_block("ESIXTKAPPAIN", input.TKappaInput);
   input.LambdaxInput = slha_io.read_entry("ESIXRUNIN", 1);
   input.TLambdaxInput = slha_io.read_entry("ESIXRUNIN", 2);
   slha_io.read_block("ESIXLAMBDAIN", input.Lambda12Input);
   slha_io.read_block("ESIXTLAMBDAIN", input.TLambda12Input);

}

void NE6SSM_slha_io::fill(Spectrum_generator_settings& settings) const
{
   SLHA_io::Tuple_processor flexiblesusy_processor
      = boost::bind(&NE6SSM_slha_io::fill_flexiblesusy_tuple, boost::ref(settings), _1, _2);

   slha_io.read_block("FlexibleSUSY", flexiblesusy_processor);
}

void NE6SSM_slha_io::fill_minpar_tuple(NE6SSM_input_parameters& input,
                                                int key, double value)
{
   switch (key) {
   case 3: input.TanBeta = value; break;
   default: WARNING("Unrecognized key: " << key); break;
   }

}

void NE6SSM_slha_io::fill_extpar_tuple(NE6SSM_input_parameters& input,
                                                int key, double value)
{
   // key 0 is the model parameter input scale, which is read in
   // slha_io.{hpp,cpp}
   if (key == 0)
      return;

   switch (key) {
   case 65: input.vSInput = value; break;
   case 63: input.muPrimeInput = value; break;
   case 64: input.BmuPrimeInput = value; break;
   case 72: input.QS = value; break;
   default: WARNING("Unrecognized key: " << key); break;
   }

}

void NE6SSM_slha_io::fill_flexiblesusy_tuple(Spectrum_generator_settings& settings,
                                                  int key, double value)
{
   if (0 <= key && key < static_cast<int>(Spectrum_generator_settings::NUMBER_OF_OPTIONS)) {
      settings.set((Spectrum_generator_settings::Settings)key, value);
   } else {
      WARNING("Unrecognized key in block FlexibleSUSY: " << key);
   }
}

/**
 * Reads the renormalization scales from all DR-bar parameter blocks.
 * If blocks with different scales are found the last scale is
 * returned and a warning is printed.
 *
 * @return common renormalization scale
 */
double NE6SSM_slha_io::read_scale() const
{
   double scale = 0.;

   for (unsigned i = 0; i < NUMBER_OF_DRBAR_BLOCKS; i++) {
      const double block_scale = slha_io.read_scale(drbar_blocks[i]);
      if (!is_zero(block_scale)) {
         if (!is_zero(scale) && !is_equal(scale, block_scale))
            WARNING("DR-bar parameters defined at different scales");
         scale = block_scale;
      }
   }

   return scale;
}

} // namespace flexiblesusy
