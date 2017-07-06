#!/usr/bin/perl

# addp.pl: Digi device detection and control via ADDP and SNMP

# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.

# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.

# You should have received a copy of the GNU General Public License
# along with this program.  If not, see <http://www.gnu.org/licenses/>.

####

# TODO: Obtain Digi Wifi device to see if more addp codes come back.
# TODO: Obtain Digi MEI device to see is more snmp codes come back
# TODO: verify implementation of DVKT. I don't have a development kit.
# not TODO: ipv6, no evidence that it is documented or implemented in any Digi utility..
#   There are more switches in the addp readme but they appear to be not implemented.
# TODO: should we add -q -m MAC1,MAC2,MAC3
# TODO: I've read that some devices require an encrypted password.
# TODO: What is ADDP response code 25? Reported by PortServer TS, not reported by Digi One SP.
# not TODO: Try to support B&B VESP, a Digi OEM product. Structures are completely different.
# TODO: Provide code to WireShark team so they can decode these packets
# TODO: Improve SNMP name detection with more Digi models.
# TODO: ADDP repeater/proxy to allow scans on distant networks.

# TODO: Finalize location of drpadmin
# TODO: Set g_src when github is done

# http://www.digi.com/wiki/developer/index.php/Advanced_Device_Discovery_Protocol_(ADDP)
# http://qbeukes.blogspot.com/2009/11/advanced-digi-discovery-protocol_21.html
# https://github.com/christophgysin/addp

# This is a remake of Digi's ADDP and SDDP in Perl. Digi does not supply a 64 bit version of ADDP
# and Digi ADDP does not produce a brief output suitable for use in drpadmin.
# This is named addp.pl instead of addp to avoid conflicting with any addp
# already installed. Tab completion will show it.

# The ADDP protocol is Copyright (C) Digi Corporation

# Related Digi Programs
# 81000137_X.tgz  dgrp: tty driver in C source
# 40002188_H.tgz  Digi Port Authority DPA: SNMP and ADDP gui in tcl/tk, aging badly, hard to get working.
# 40002188_H.tgz  sddp: SNMP cli in compiled C
# 40002889_A.tgz  addp: cli in compiled C, also 40002890_A.tgz
# addplib-1.0.jar ADDP Library: sdk in java
# AddpClient.jar  Digi Device Discovery Tool: ADDP gui in java, lots of inaccurate codes
# Digi DCRabbit, https://github.com/digidotcom/DCRabbit_10
# netos74, not generally available

# Related non Digi programs
# drpadmin: A remake for Linux dgrp of the tui drpadmin found in SCO, HP UX, and Solaris
# Metasploit::addp.rb https://github.com/rapid7/metasploit-fraamework/blob/master/lib/rex/proto/addp.rb

use strict;
use warnings;
use integer; # Changes bitwise operations to signed. Signed is useless if you can't control the size.
use bytes;
no utf8;
no overloading;
no locale;

use Socket qw(PF_INET SOCK_STREAM pack_sockaddr_in inet_aton);
use IO::Socket;
#use IO::Socket::Multicast;
use IO::Select;
use Socket qw(IPPROTO_TCP TCP_NODELAY);
use Time::HiRes qw(gettimeofday tv_interval usleep);
use Getopt::Long qw(:config bundling no_ignore_case no_auto_abbrev no_getopt_compat no_permute require_order);
use Data::Dumper;

my $g_src='github: addp.pl';

sub usage {
  my $usage= <<EOF;
Commands: -Q -q -R -S
Usage examples:
addp.pl -Q # query all devices
addp.pl -Q --snmp # query all devices ADDP and SNMP. This catches non ADDP devices like the PortServer II. Name detection isn't perfect.
addp.pl -q -m 000001 -n 192.168.1.5 # Using only the specified interface, query specific device with MAC scanned from short Digi MAC barcode label.
addp.pl -R -m 000000000001 # reboot device with the default password with MAC scanned from long Digi MAC barcode label.
addp.pl -S -m 00-00-00-00-00-01 -d # set device to DHCP with the default password and Windows MAC format. -d On also works.
addp.pl -S -m 00-00-00-00-00-01 -d Off # set device to static with current settings. Avoid this because it can leave the unit unreachable at address 0.0.0.0. Use -S.
addp.pl -R -m 00:00:00:00:00:01 -S -d -p '1234' # set device to DHCP and reboot using specified password. -R and -S can be in any order.
addp.pl -S -m 00:00:00:00:00:01 -a 192.168.1.50/24 -g 0.0.0.0 # set device to static IP with no gateway.
addp.pl -S -m 00:00:00:00:00:01 -a 192.168.1.50 -s 255.255.255.0 -g 192.168.1.1 # set device to static IP with gateway.
addp.pl -S # show which options are needed for -S
addp.pl -S -d # show which remaining options are still needed for -S
addp.pl -S -d -a 192.168.50.50/24 # Conflicting options will get you nowhere.
See source for other less common commands and options.
EOF
#addp.pl -Q -addip 10.1.10.10 # Query ADDP device across VPN
#addp.pl -R -addip 10.1.10.10 # Reboot ADDP device across VPN. MAC will be retrieved automatically or you can supply it with -m
  print $usage;
  exit 1;
}
usage() if (scalar @ARGV == 0);

my $opt_IPAddress='';
my $opt_IPSubnet='';     # can be derived from IP specified like 192.168.1.10/24
my $opt_MACAddress='';
my $opt_BindAddress='';
my $opt_IPGateway='';
my $opt_DHCP;
my $DefaultPassword="dbps";
my $opt_Password;        # -p '' is allowed. Digi Device Discovery Tool tries blank passwords first.
my $opt_QueryAll=0;
my $opt_QueryMAC=0;
my $opt_SaveSettings=0;
my $opt_RebootDevice=0;

my $opt_TimeoutS=2;      # Timeout in seconds to wait for multiple queries to return. This time isn't exact.
my $opt_Debug=0;         # 0=normal responses, 1=debug received responses, 2=debug sent and received responses
my $opt_Quiet=0;         # supress normal responses. -Q or -q responses cannot be suppressed
my $opt_LimitQuery=0;    # 0 for all results, >0 to only show n results or less. Usually used with --query-short.
my $opt_BackingStore=''; # '' for all results, /etc/dgrp.backing.store to supress output of already configured devices
my $opt_QueryShort=0;    # 0 for full detail, 1 for a one line summary. 1 enables SNMP searches to catch non addp Digi products.
my %BackingStore;        # $_{$ip}=1 foreach ip in the backing store
my $opt_Version=0;       # Show version and exit. Can be combined with 1 or more --quiet to remove version cruft.
my $opt_DataDump='';     # Dump transmit and responses to a file. May help with bug reports.
my $opt_DataRead='';     # Read and decode responses from file. Usually used with --debug.
my $opt_SNMP='';         # Perform SNMP broadcasts along with addp. Only works with -Q for broadcasts.
my $opt_DecodeAddp='';   # Decode addp from Wireshark copy bytes hex stream (data only)
# addp.pl --debug=1 --decode-addp '44564b540001001cffffffffffff1510bf6db409c83d44a3a36d21797d2f73f914020200'
my $opt_Magic='DIGI';    # Specify alternate magic. See %ADDP_MAGICS. You can specify any 4 letter magic you like but things won't well well if you just make one up. The GUIs reuse the magic from received responses.
my $opt_GUID;            # Specify alternate GUID.
my $opt_Vendor;          # Specify Vendor for GUID.
my $DefaultAddpIP="224.0.5.128";
my $opt_AddpIP;          # Send addp packets directly to the IP instead of the multicast.
  # Makes it harder for eavesdroppers to capture passwords in -R and -S packets.
  # Can be used with -Q to find the MAC address of units behind routers and across VPN.
  # Used with -R or -S, the MAC can be left off and it will be retrieved automatically.
  # This allows reboot or configuration of units across routers without having to manually retrieve the MAC.
my $opt_SignedBytes='';  # Convert a series of signed integers to hex bytes. Read the GUID from VendorGuid.class
my $opt_ConflictOverride=0; # Lets you specify any command line options you want. Might be dangerous, cause strange errors, or crash the program. Mainly used for making the program. If you need it for something useful that works then it's a bug that should be reported.

# These options are made to be as close to addp as possible so this can be a drop in replacement for as much as we support.
GetOptions(
"ip-address|a=s" => \$opt_IPAddress,
"ip-subnet|s=s"  => \$opt_IPSubnet,
"mac-address|m=s"=> \$opt_MACAddress,
"interface|n=s"  => \$opt_BindAddress,
"ip-gateway|g=s" => \$opt_IPGateway,
"use-dhcp|d:s"   => \$opt_DHCP,
"password|p=s"   => \$opt_Password,
"query-all|Q"    => \$opt_QueryAll,
"query-mac|q"    => \$opt_QueryMAC,
# Todo: -C return a list of available country codes (Wireless only)
"save-settings|S"=> \$opt_SaveSettings,
"reboot-device|R"=> \$opt_RebootDevice,
# Todo: -W Save wireless settings
# Todo: -I Auto ssid
# Todo: -e encryption
# Todo: -i ssid string
# Todo: -A Network authentication
# Todo: -P TX Enhanced power
# Todo: -k Encryption key
# Todo: -c country code

# According to the getopts string in addp, these missing options are not implemented in addp.
# I can't find them in DPA.
# Some are implemented in addplib-1.0.jar

# new options, long form only!
"timeout=i"         => \$opt_TimeoutS,
"debug=i"           => \$opt_Debug,
"quiet+"            => \$opt_Quiet,
"limit-query=i"     => \$opt_LimitQuery,
"backing-store=s"   => \$opt_BackingStore,
"query-short"       => \$opt_QueryShort,
"version"           => \$opt_Version,
"data-dump=s"       => \$opt_DataDump,
"data-read=s"       => \$opt_DataRead,
"snmp"              => \$opt_SNMP,
"decode-addp=s"     => \$opt_DecodeAddp, # no point in decode-snmp. Wireshark already does this though somewhat less informative than we do.
"magic=s"           => \$opt_Magic,
"guid=s"            => \$opt_GUID,
"vendor=i"          => \$opt_Vendor,
"addpip=s"          => \$opt_AddpIP,
"signed-bytes=s"    => \$opt_SignedBytes,
"conflict-override" => \$opt_ConflictOverride,
) or die("Error in command line arguments\n");

if ($opt_Version) {
  # Do not add comments to or change the quotes on the next lines. They are expected to be sed by distros.
  my $distro='Arch Linux';
  my $version='1.0';
  if ($opt_Quiet==2) {
    printf("%s",$version);
  } elsif ($opt_Quiet==1) {
    printf("%s-%s",$version,$distro);
  } else {
    printf("Version %s for %s\n",$version,$distro);
  }
  exit(0);
}

# converts to a number decimal, octal, or hex. Binary is not accepted.
# to duplicate what Windows ping accepts
# Desirable numbers range from 0 to 255
# Returns >255 for invalid or negative numbers
sub hexOctDec {
  my ($arg_num)=(@_);
  #print STDERR "hexOctDec Checking ".$arg_num."\n";
  return 256 if (not defined($arg_num));
  return oct($arg_num) if ($arg_num =~ m/^0[0-7]+/ or $arg_num =~ m/^0[xX][[:xdigit:]]+/);
  return $arg_num+0 if ($arg_num =~ m/^\d+$/); # leading 0 taken above
  return 256; # we don't accept 0b binary or text
}

sub hexOctDecCheck {
  if (hexOctDec('0b111') != 256
   or hexOctDec('0x101') != 257
   or hexOctDec('0401') != 257
   or hexOctDec('www') != 256
   or hexOctDec('0ww') != 256
   or hexOctDec('') != 256
   or hexOctDec('-6') != 256
   ) {
    die("hexOctDecCheck failed\n");
  }
}
hexOctDecCheck() if ($opt_Debug);

# Return 0 if valid, 1 if not valid
# $subnet: 0=normal IP check, 1=must be valid CIDR subnet
sub isNotValidIP {
  my ($arg_ip,$arg_subnet)=(@_);
  if (length($arg_ip)) {
    # Strawberry perl 5.24 inet_aton("255.255.255.256") pauses for a few seconds trying to calculate this.
    # inet_aton does DNS lookups on addresses it can't convert to numbers like 255.255.255.256 or www.google.com.
    # We accept IP addresses only, including octal and hex because, anoyingly enough, Windows ping accepts this
    # ping 0x0A.1.012.1 to ping a cable modem at 10.1.10.1
    my @ips=split(/\./,$arg_ip);
    return 1 if (scalar @ips != 4);
    foreach (@ips) {
      return 1 if (hexOctDec($_)>255);
    }
    my $ipn=inet_aton($arg_ip);
    if (not defined $ipn) { return 1; }
    if ($arg_subnet) {
      my $ipb=unpack("B*",$ipn);
      if (not $ipb =~ m/^1*0*$/) { return 1; }
    }
  }
  return 0;
}
#print isNotValidIP('128.0.0.1',0); die();

# early fixes to options
sub optfixup {
  if (length($opt_IPSubnet)==0 and $opt_IPAddress =~ m/^([^\/]+)\/([0-9]{1,2})$/ and isNotValidIP($1,0)==0 and $2>0 and $2<=32) {
    $opt_IPAddress=$1;
    $opt_IPSubnet=inet_ntoa(pack("N",oct("0b"."1" x $2."0" x (32-$2))));
  }
}
optfixup();

# From AddpClient.jar MagicCookie.class and http://ftp1.digi.com/support/documentation/html/90001429/com/digi/addp/AddpClient.html
my %ADDP_MAGICS=(
  'DIGI' => "Digi Commercial Products",
  'DVKT' => "Digi Development Kit (new)", # NetSilicon
  'DGDP' => "Digi Development Kit (pre 6.0)",
);

# from AddpClient.jar VendorGuid.class. Converted with option --signed-bytes
my %ADDP_GUIDS=(
  'NETSILICON' => "bf6db409-c83d-44a3-a36d-21797d2f73f9",
  'DIGI'       => "fbb24a71-1ff7-4ade-f54d-3b1fb24d2941",
  'INSIDE'     => "e34e79d8-1c5d-40a1-e60a-33b9eef78837",
  'EMBRACE'    => "e42a6f12-b212-4e05-fb6c-2f9c8b28ad59",
);

# $arg_mac: the MAC address in one of many text forms like "00:00:00:00:00:00"
# $arg_short: 1 if short MAC 00:00:00 is allowed, 0 if full 12 digit MAC is required
# return: 0 if MAC is valid, 1 if MAC is not valid
# an empty MAC is considered invalid
# Copy-paste mistakes are permitted:  -00-00-00  :00:00:00
# Slop variations not allowed: 00-00-00:00:00:00 0000:00
sub isNotValidMAC {
  my ($arg_mac,$arg_short)=(@_);
  $arg_mac=lc $arg_mac;
  $arg_mac =~ tr/123456789abcdef/000000000000000/ ;
  #printf STDERR ("Testing MAC %s, short=%u\n",$arg_mac,$arg_short);
  return 1 if (length($arg_mac)==0);
  return 0 if ($arg_mac eq '00:00:00:00:00:00' or $arg_mac eq '00-00-00-00-00-00' or $arg_mac eq '000000000000');
  return 1 if (not $arg_short);
  return 0 if ($arg_mac eq ':00:00:00' or $arg_mac eq '-00-00-00' or $arg_mac eq '00:00:00' or $arg_mac eq '00-00-00' or $arg_mac eq '000000');
  return 1;
}

# Check option values for bad formatting or out of rage.
# Options are modified after being shown to the user in their original form.
# We blank out or correct invalid values to prevent more checking. Improper values can be blanked out but it's not necessary.
use constant {
  ADDP_OPCODE_MAGIC_LEN           => 4,
};
sub opterrors {
  my $errors=0;
  if (length($opt_Magic) != ADDP_OPCODE_MAGIC_LEN) {
    printf STDERR ("--magic is %u characters. Try %s\n",ADDP_OPCODE_MAGIC_LEN,join(" ",sort keys %ADDP_MAGICS));
    $errors++;
    $opt_Magic='';
  }
  if ($opt_Debug<0) {
    printf STDERR ("--debug <0, let's not!\n");
    $errors++;
    $opt_Debug=0;
  }
  if (length($opt_MACAddress) and isNotValidMAC($opt_MACAddress,1)) {
    printf STDERR ("Invalid MAC address %s\n",$opt_MACAddress);
    $errors++;
    $opt_MACAddress='';
  }
  if (isNotValidIP($opt_BindAddress,0)) {
    printf STDERR ("Invalid IP address -a %s\n",$opt_BindAddress);
    $errors++;
    $opt_BindAddress='';
  }
  if (isNotValidIP($opt_IPAddress,0)) {
    printf STDERR ("Invalid IP address -a %s\n",$opt_IPAddress);
    $errors++;
    $opt_IPAddress='';
  }
  if (isNotValidIP($opt_IPSubnet,1)) {
    printf STDERR ("Invalid subnet -s %s\n",$opt_IPSubnet);
    $errors++;
    $opt_IPSubnet='';
  }
  if (isNotValidIP($opt_IPGateway,0)) {
    printf STDERR ("Invalid gateway -g %s\n",$opt_IPGateway);
    $errors++;
    $opt_IPGateway='';
  }
  if (length($opt_IPAddress) and length($opt_IPSubnet) and length($opt_IPGateway)) {
    my $iperrors=0;
    my $i=inet_aton($opt_IPAddress);
    my $s=inet_aton($opt_IPSubnet);
    my $sn=unpack("B*",$s); $sn =~ /^(1*)0*$/; $sn=length($1);
    my $g=inet_aton($opt_IPGateway);
    if ( inet_ntoa($g) ne '0.0.0.0' and inet_ntoa($i & $s) ne inet_ntoa($g & $s) ){ # We could have used cmp but this is already done.
      printf STDERR ("Gateway -g %s not in subnet of -a %s\n",$opt_IPGateway,$opt_IPAddress);
      $iperrors++;
    }
    if ($sn < 31) { # no broadcast on /31 or /32
      my $ig=inet_ntoa($i);
      if ( $ig eq inet_ntoa($i | ~$s) or $ig eq inet_ntoa($i & $s) ){
        printf STDERR ("ip -a %s cannot be broadcast\n",$opt_IPAddress);
        $iperrors++;
      }
      $ig=inet_ntoa($g);
      if ( $ig ne '0.0.0.0' and ($ig eq inet_ntoa($g | ~$s) or $ig eq inet_ntoa($g & $s)) ){
        printf STDERR ("gateway -g %s cannot be broadcast\n",$opt_IPGateway);
        $iperrors++;
      }
    }
    if ($iperrors) {
      $errors += $iperrors;
      $opt_IPAddress='';
      $opt_IPSubnet='';
      $opt_IPGateway='';
    }
  }
  if (length($opt_IPAddress) and length($opt_IPGateway)) {
    my $i=inet_aton($opt_IPAddress);
    my $g=inet_aton($opt_IPGateway);
    if ( inet_ntoa($i) eq inet_ntoa($g) ){
      printf STDERR ("Gateway -g %s cannot be same as IP -a %s\n",$opt_IPGateway,$opt_IPAddress);
      $errors++;
      $opt_IPAddress='';
      $opt_IPGateway='';
    }
  }
  if ($opt_TimeoutS<1 or $opt_TimeoutS>100) {
    printf STDERR ("--timeout must be between 1 and 100 seconds\n");
    $errors++;
    $opt_TimeoutS=1;
  }
  if ($opt_LimitQuery<0) {
    printf STDERR ("--limit-query must be >=0\n");
    $errors++;
    $opt_LimitQuery=0;
  }
  if (defined $opt_GUID)  {
    my $guid=$opt_GUID;
    $guid =~ s/-//g;
    if (not $ADDP_GUIDS{uc $guid} and not $guid =~ m/^[[:xdigit:]]{32}$/ ) {
      print STDERR "--guid must be 32 hex digits or one of the builtins\n";
      print STDERR join(" ",sort keys %ADDP_GUIDS),"\n";
      $errors++;
      undef $opt_GUID;
    }
  }
  if (defined $opt_Vendor and ($opt_Vendor<0 or $opt_Vendor>65535))  {
    print STDERR "--vendor ranges from 0-65535\n";
    $errors++;
    undef $opt_Vendor;
  }
  if (defined $opt_AddpIP) {
    if (isNotValidIP($opt_AddpIP,0)) {
      printf STDERR ("--addpip %s not valid IP\n",$opt_AddpIP);
      $errors++;
      $opt_AddpIP='';
    } else {
      my $i=inet_aton($opt_AddpIP);
      if ( inet_ntoa($i) eq '255.255.255.255' ) {
        printf STDERR ("--addpip %s cannot be broadcast. Digi ADDP devices don't respond to it.\nYou can try the broadcast for your subnet but you'll find that doesn't work either.\n",$opt_AddpIP);
        $errors++;
      }
    }
  }
  return $errors;
}

# check for option conflicts and optional requirements.
# This functions as a rudimentary help for options
sub optconflicts {
  my $errors=0;
  {
    my $xcmd=sprintf("%s%s%s",
        ,length($opt_DataRead)?"--data-read ":""
        ,length($opt_DecodeAddp)?"--decode-addp ":""
        ,length($opt_SignedBytes)?"--signed-bytes ":""
      ); # Don't show these unless asked for
    my $cmds=($opt_QueryMAC?1:0) + ($opt_SaveSettings?1:0) + (length($opt_DataRead)?1:0) + (length($opt_DecodeAddp)?1:0) + (length($opt_SignedBytes)?1:0);
    if ( ($opt_QueryAll?1:0) + $cmds + ($opt_RebootDevice?1:0) == 0) {
      print STDERR "Must specify one or more of -Q -q -S -R\n";
      $errors++;
    } elsif ( ($opt_QueryAll?1:0) + $cmds > 1 ) {
      printf STDERR ("Commands -Q -q -S %scannot be stacked. -R stacks with some commands.\n",$xcmd);
      $errors++;
    }
    if ($cmds and $opt_SNMP) {
      printf STDERR ("--snmp only works with -Q, can't be used with -q -S -R %s\n",$xcmd);
      $errors++;
    }
  }
  if ($opt_QueryAll or $opt_QueryMAC) {
    if ($opt_QueryAll) {
      if (length($opt_MACAddress)) {
        print STDERR "-m MAC cannot be used with -Q, try -q\n";
        $errors++;
      }
      # Turns out this is useful for learning the MAC of a remote device.
      #if (defined $opt_AddpIP) {
      #  print STDERR "--addpip is not useful with -Q. Only local subnets can be scanned. Try -q\n";
      #  $errors++;
      #}
    } else {
      if ($opt_LimitQuery) {
        print STDERR "--limit-query can only be used with -Q\n";
        $errors++;
      }
      if ($opt_BackingStore) {
        print STDERR "--backing-store can only be used with -Q\n";
        $errors++;
      }
      if ($opt_QueryShort) {
        print STDERR "--query-short can only be used with -Q\n";
        $errors++;
      }
    }
# Replaced below
#    if ($opt_QueryMAC) {
#      if (length($opt_MACAddress)==0) {
#        print STDERR "-m MAC is required for -q. Try -Q to scan all.\n";
#        $errors++;
#      }
#    }
    if (length($opt_IPAddress)) {
      print STDERR "-a IPAddress cannot be used with -Q -q\n";
      $errors++;
    }
    if (length($opt_IPSubnet)) {
      print STDERR "-s subnet cannot be used with -Q -q\n";
      $errors++;
    }
    if (length($opt_IPGateway)) {
      print STDERR "-g gateway cannot be used with -Q -q\n";
      $errors++;
    }
    if (defined $opt_DHCP) {
      print STDERR "-d DHCP cannot be used with -Q -q\n";
      $errors++;
    }
    if (defined $opt_Password) {
      print STDERR "-p password cannot be used with -Q -q\n";
      $errors++;
    }
    if ($opt_SaveSettings) {
      print STDERR "-S save settings cannot be used with -Q -q\n";
      $errors++;
    }
    if ($opt_RebootDevice) {
      print STDERR "-R reboot cannot be used with -Q -q\n";
      $errors++;
    }
  }
  if ($opt_QueryMAC or $opt_SaveSettings or $opt_RebootDevice) {
    if (length($opt_MACAddress) == 0) {
      if (not defined $opt_AddpIP or $DefaultAddpIP eq $opt_AddpIP or $opt_QueryMAC) {
        print STDERR "-m MAC is required for options -R -S -q\n";
        $errors++;
        if (defined $opt_AddpIP and $DefaultAddpIP ne $opt_AddpIP) {
          print STDERR "Try -Q to query from --addpip\n";
        }
      }
    } else {
      my $mac=lc $opt_MACAddress;
      $mac =~ s/[:-]//g;
      if ($mac eq 'ffffffffffff') {
        # Rebooting every Digi in the fleet would be stupid, wouldn't it? Fortunately the devices don't allow this.
        print STDERR "-m MAC cannot be broadcast for -R -S -q\n";
        $errors++;
        if ($opt_SaveSettings or $opt_RebootDevice) {
          print STDERR "Digi devices do not respond to broadcast -R or -S.\n";
        }
        if ($opt_QueryMAC) {
          print STDERR "try -Q to query all\n";
        }
      }
    }
  }
  if ($opt_SaveSettings) {
    if (not defined $opt_DHCP) {
      my $optdhcperrors=0;
      if (length($opt_IPAddress)==0) {
        print STDERR "-a IPAddress is required for option -S\n";
        $errors++;
        $optdhcperrors++;
      }
      if (length($opt_IPSubnet)==0) {
        print STDERR "-s subnet or -a with /netmask is required for option -S\n";
        $errors++;
        $optdhcperrors++;
      }
      if (length($opt_IPGateway)==0) {
        print STDERR "-g gateway is required for option -S. Specify 0.0.0.0 for no gateway\n";
        $errors++;
        $optdhcperrors++;
      }
      if ($optdhcperrors) {
        print STDERR "alternately, -d DHCP can be used with option -S\n";
      }
    }
  } else {
    if (length($opt_IPAddress)) {
      print STDERR "-a IPAddress requires option -S\n";
      $errors++;
    }
    if (length($opt_IPSubnet)) {
      print STDERR "-s subnet requires option -S\n";
      $errors++;
    }
    if (length($opt_IPGateway)) {
      print STDERR "-g gateway requires option -S\n";
      $errors++;
    }
    if (defined $opt_DHCP) {
      print STDERR "-d DHCP requires option -S\n";
      $errors++;
    }
  }
  if (defined $opt_DHCP) {
    if (not(length($opt_DHCP)==0 or lc $opt_DHCP eq 'on' or lc $opt_DHCP eq 'off')) {
      print STDERR "option -d must be blank, on, or off\n";
      $errors++;
    }
    if (length($opt_IPAddress)) {
      print STDERR "-a IPAddress cannot be combined with option -d DHCP\n";
      $errors++;
    }
    if (length($opt_IPSubnet)) {
      print STDERR "-s subnet cannot be combined with option -d DHCP\n";
      $errors++;
    }
    if (length($opt_IPGateway)) {
      print STDERR "-g gateway cannot be combined with option -d DHCP\n";
      $errors++;
    }
  }
  if ($opt_Quiet) {
    if ($opt_Debug) {
      print STDERR "--quiet and --debug don't make sense together.\n";
      $errors++;
    }
    if (length($opt_DataRead))  {
      print STDERR "--quiet and --data-read don't make sense together.\n";
      $errors++;
    }
  }
  if (length($opt_DataRead))  {
    if (length($opt_IPAddress)) {
      print STDERR "-a IPAddress cannot be used with --data-read\n";
      $errors++;
    }
    if (length($opt_IPSubnet)) {
      print STDERR "-s subnet cannot be used with --data-read\n";
      $errors++;
    }
    if (length($opt_IPGateway)) {
      print STDERR "-g gateway cannot be used with --data-read\n";
      $errors++;
    }
    if (defined $opt_DHCP) {
      print STDERR "-d DHCP cannot be used with --data-read\n";
      $errors++;
    }
    if (defined $opt_Password) {
      print STDERR "-p password cannot be used with --data-read\n";
      $errors++;
    }
  }
  if ($opt_SNMP)  {
    if (length($opt_IPAddress)) {
      print STDERR "-a IPAddress cannot be used with --data-read\n";
      $errors++;
    }
    if (length($opt_IPSubnet)) {
      print STDERR "-s subnet cannot be used with --data-read\n";
      $errors++;
    }
    if (length($opt_IPGateway)) {
      print STDERR "-g gateway cannot be used with --data-read\n";
      $errors++;
    }
    if (defined $opt_DHCP) {
      print STDERR "-d DHCP cannot be used with --data-read\n";
      $errors++;
    }
    if (defined $opt_Password) {
      print STDERR "-p password cannot be used with --data-read\n";
      $errors++;
    }
  }
  if (length($opt_DataDump) and length($opt_DataRead))  {
    print STDERR "--data-dump and --data-read cannot be specified together\n";
    $errors++;
  }
  if (defined $opt_Vendor != defined $opt_GUID) { # boolean xor
    print STDERR "--vendor and --guid must be specified together\n";
    $errors++;
  }
  return $errors;
}

{
  my $err=opterrors();  # ensure we see messages from both
  my $con=optconflicts();
  die("Error in command line arguments\n") if ( $err or $con and not $opt_ConflictOverride);
  print STDERR "Override, continuing. This program might crash or behave unexpectedly.\n" if ($con);
}

sub optclean_MAC {
  if (length($opt_MACAddress)) {
    $opt_MACAddress = lc $opt_MACAddress;
    $opt_MACAddress =~ s/[:-]//g;
    if (length($opt_MACAddress)==6 ) {
      $opt_MACAddress="00409d".$opt_MACAddress; # Digi OID
    }
  }
}

# Here we clean and fix various arguments for easy use below.
sub optclean {
  $opt_Password=$DefaultPassword if (not defined $opt_Password);
  # We don't pack("H*") the MAC address because we need to string compare it down below
  optclean_MAC();
  $opt_IPAddress=inet_ntoa(inet_aton($opt_IPAddress)) if (length($opt_IPAddress));
  $opt_IPSubnet =inet_ntoa(inet_aton($opt_IPSubnet))  if (length($opt_IPSubnet));
  $opt_IPGateway=inet_ntoa(inet_aton($opt_IPGateway)) if (length($opt_IPGateway));
  if ($opt_GUID) {
    $opt_GUID=$ADDP_GUIDS{uc $opt_GUID} if ($ADDP_GUIDS{uc $opt_GUID});
    $opt_GUID =~ s/-//g;
    $opt_GUID=pack("H*",$opt_GUID);
  }
  $opt_AddpIP=$DefaultAddpIP if (not defined $opt_AddpIP);
}
optclean();

sub readBackingStore {
  if (not open(my $fh, '<', $opt_BackingStore)) {
    printf STDERR ("--backing-store file not found %s\n",$opt_BackingStore);
  } else {
    my @row;
    my $ip;
    while(my $row=<$fh>) {
      if ($row =~ m/^[a-z]{1,2}\s+[0-9]/ ) {
        @row=split(/\s+/,$row);
        $ip=$row[1];
        if (isNotValidIP($ip,0)==0) {
          $BackingStore{$ip}=1;
        }
      }
    }
    close($fh);
  }
}
readBackingStore() if ($opt_BackingStore);

# http://perldoc.perl.org/constant.html#CAVEATS
use constant {
  ADDP_PACKET_DISCOVERY_REQUEST         => 0x0001, # CONF
  ADDP_PACKET_DISCOVERY_RESPONSE        => 0x0002,
  ADDP_PACKET_STATIC_NETCONFIG_REQUEST  => 0x0003, # ADDR
  ADDP_PACKET_STATIC_NETCONFIG_RESPONSE => 0x0004,
  ADDP_PACKET_REBOOT_REQUEST            => 0x0005, # REBOOT
  ADDP_PACKET_REBOOT_RESPONSE           => 0x0006,
  ADDP_PACKET_DHCP_REQUEST              => 0x0007, # WL
  ADDP_PACKET_DHCP_RESPONSE             => 0x0008,
# CMD_SET_WL_REQ = 9 # from Metasploit addp.rb
# CMD_SET_WL_REP = 10
# CMD_SET_WL_COUNTRIES_REQ = 11
# CMD_SET_WL_COUNTRIES_REP = 12
#  ADDP_PACKET_EDP_REQUEST               => 13, # From AddpClient.class, Digi Device Cloud EDP
#  ADDP_PACKET_CMD_CONT                  => 14, # Appears to not be a reply of 13. From addplib-1.0.jar MessageType.class
};

my %ADDP_PACKET_NAME=(
  ADDP_PACKET_DISCOVERY_REQUEST        ,'Discovery Request',
  ADDP_PACKET_DISCOVERY_RESPONSE       ,'Discovery Response',
  ADDP_PACKET_STATIC_NETCONFIG_REQUEST ,'Static Request',
  ADDP_PACKET_STATIC_NETCONFIG_RESPONSE,'Static Response',
  ADDP_PACKET_REBOOT_REQUEST           ,'Reboot Request',
  ADDP_PACKET_REBOOT_RESPONSE          ,'Reboot Response',
  ADDP_PACKET_DHCP_REQUEST             ,'DHCP Request',
  ADDP_PACKET_DHCP_RESPONSE            ,'DHCP Response',
);

use constant {
  ADDP_OPCODE_MAC          =>0x01,
  ADDP_OPCODE_IPADDR       =>0x02,
  ADDP_OPCODE_SUBMASK      =>0x03,
  ADDP_OPCODE_NETNAME      =>0x04, # Supressed if blank. addp shows (null)
  ADDP_OPCODE_DOMAIN       =>0x05,
  ADDP_OPCODE_HWTYPE       =>0x06,
  ADDP_OPCODE_HWREV        =>0x07,
  ADDP_OPCODE_FIRMWARE     =>0x08, # ADDP_FEPREV
  ADDP_OPCODE_RESULTMESSAGE=>0x09, # ADDP_MSG
  ADDP_OPCODE_RESULTFLAG   =>0x0A, # 10 # ADDP_RESULT
  ADDP_OPCODE_GATEWAY      =>0x0B, # 11
  ADDP_OPCODE_CONFIGERR    =>0x0C, # 12 # ADDP_ADVIOSRY [sic]
  ADDP_OPCODE_HWNAME       =>0x0D, # 13
  ADDP_OPCODE_REALPORT     =>0x0E, # 14
  ADDP_OPCODE_DNS          =>0x0F, # 15
  ADDP_OPCODE_DHCP         =>0x10, # 16
  ADDP_OPCODE_ERRCODE      =>0x11, # 17
  ADDP_OPCODE_PORT_CNT     =>0x12, # 18
  ADDP_OPCODE_SECURE_RP    =>0x13, # 19
  ADDP_OPCODE_VERSION      =>0x14, # 20
  ADDP_OPCODE_VENDORGUID   =>0x15, # 21
#  ADDP_OPCODE_IF_TYPE      =>22, # From DeviceData.class in AddpClient.jar, and PayloadOpCode.class in addplib-1.0.jar
#  ADDP_OPCODE_AF_CHALLENGE =>23, # From DeviceData.class
#  ADDP_OPCODE_AF_CAP_PORT  =>24, # From DeviceData.class
  ADDP_OPCODE_UNKNOWN19    =>0x19, # 25 not defined in DeviceData.class, unknown in Metasploit addp.rb, not defined in PayloadOpCode.class
  # It's returned by PortServer TS. Does noone at Digi know what this is?
#  ADDP_OPCODE_EDP_DEVID    =>26, # From DeviceData.class
#  ADDP_OPCODE_EDP_ENABLED  =>27, # From DeviceData.class
#  ADDP_OPCODE_EDP_URL      =>28, # From DeviceData.class
#  ADDP_OPCODE_WL_SSID      =>224, # From DeviceData.class
#  ADDP_OPCODE_WL_AUTO_SSID =>225, # From DeviceData.class
#  ADDP_OPCODE_WL_TX_ENH_POWR,226, # From DeviceData.class
#  ADDP_OPCODE_WL_AUTH_MODE =>227, # From DeviceData.class
#  ADDP_OPCODE_WL_ENC_MODE  =>228, # From DeviceData.class
#  ADDP_OPCODE_WL_ENC_KEY   =>229, # From DeviceData.class
#  ADDP_OPCODE_WL_CUR_COUNTRY=>230, # From DeviceData.class
#  ADDP_OPCODE_WL_COUNTRY_LIST=>231, # From DeviceData.class
};

# We only leave in the constants used for sending. Received item sizes are specified in the returned packet.
# Noone notices all the invalid lengths because they are never used.
use constant { #-1 = unlimited length
  ADDP_OPCODE_MAC_LEN             => 6,
  ADDP_OPCODE_IPADDR_LEN          => 4,
  ADDP_OPCODE_SUBMASK_LEN         => 4,
  #ADDP_OPCODE_NETNAME_LEN         => -1,
  #ADDP_OPCODE_DOMAIN_LEN          => -1,
  #ADDP_OPCODE_HWTYPE_LEN          => 1,
  #ADDP_OPCODE_HWREV_LEN           => 1,
  #ADDP_OPCODE_FIRMWARE_LEN        => -1,
  #ADDP_OPCODE_RESULTMSG_LEN       => -1,
  #ADDP_OPCODE_RESULTFLAG_LEN      => 1,
  ADDP_OPCODE_GATEWAY_LEN         => 4,
  #ADDP_OPCODE_CONFIGERR_LEN       => 2, # Should be 1
  #ADDP_OPCODE_HWNAME_LEN          => -1,
  #ADDP_OPCODE_REALPORT_LEN        => 4, # 2 in PayloadOpCode.class
  #ADDP_OPCODE_DNS_LEN             => 4,
  #ADDP_OPCODE_DHCP_LEN            => 4, # 1 in PayloadOpCode.class
  #ADDP_OPCODE_ERRCODE_LEN         => 1,
  #ADDP_OPCODE_PORT_CNT_LEN        => 1,
  #ADDP_OPCODE_SECURE_RP_LEN       => 4, # 1 in PayloadOpCode.class which can't store the default port 1027. Must be at least 2.
  #ADDP_OPCODE_VERSION_LEN         => 2,
  #ADDP_OPCODE_VENDOR_GUID_LEN     => 16,
  #ADDP_OPCODE_IF_TYPE_LEN         => 1,
  #ADDP_OPCODE_CHALLENGE_LEN       => 14,
  #ADDP_OPCODE_CAP_PORT_LEN        => 2,
  #ADDP_OPCODE_EDP_DEVID_LEN       => 16,
  #ADDP_OPCODE_EDP_ENABLED_LEN     => 1,
  #ADDP_OPCODE_EDP_URL_LEN         => -1,
  #ADDP_OPCODE_WL_SSID_LEN         => -1,
  #ADDP_OPCODE_WL_AUTO_SSID_LEN    => 2,
  #ADDP_OPCODE_WL_TX_ENH_POWR_LEN  => 2,
  #ADDP_OPCODE_WL_AUTH_MODE_LEN    => 2,
  #ADDP_OPCODE_WL_ENC_MODE_LEN     => 2,
  #ADDP_OPCODE_WL_ENC_KEY_LEN      => -1,
  #ADDP_OPCODE_WL_CUR_COUNTRY_LEN  => 2,
  #ADDP_OPCODE_WL_COUNTRY_LIST_LEN => -1,
};

# These are named to closely match Digi's addp output and some vars
my %ADDP_OPCODE_FIELD=(
  ADDP_OPCODE_MAC          ,'MAC',
  ADDP_OPCODE_IPADDR       ,'IP',
  ADDP_OPCODE_SUBMASK      ,'Submask',
  ADDP_OPCODE_NETNAME      ,'Name',
  ADDP_OPCODE_DOMAIN       ,'Domain',
  ADDP_OPCODE_HWTYPE       ,'HWType',
  ADDP_OPCODE_HWREV        ,'Revision',
  ADDP_OPCODE_FIRMWARE     ,'Firmware',
  ADDP_OPCODE_RESULTMESSAGE,'Message',
  ADDP_OPCODE_RESULTFLAG   ,'Result',
  ADDP_OPCODE_GATEWAY      ,'Gateway',
  ADDP_OPCODE_CONFIGERR    ,'ConfigEr',
  ADDP_OPCODE_HWNAME       ,'Hardware',
  ADDP_OPCODE_REALPORT     ,'RealPort',
  ADDP_OPCODE_DNS          ,'DNS',
  ADDP_OPCODE_DHCP         ,'DHCP',
  ADDP_OPCODE_ERRCODE      ,'Error',
  ADDP_OPCODE_PORT_CNT     ,'Ports',
  ADDP_OPCODE_SECURE_RP    ,'SecureRP',
  ADDP_OPCODE_VERSION      ,'Version',
  ADDP_OPCODE_VENDORGUID   ,'VendGUID',
  ADDP_OPCODE_UNKNOWN19    ,'Unknown',
);
#print Dumper(\%ADDP_OPCODE_FIELD); die();
# ?=unknown, -Custom, M=MAC address, S=string, I=IP, u=unsigned number
my %ADDP_OPCODE_TYPE=(
  ADDP_OPCODE_MAC          ,'M',
  ADDP_OPCODE_IPADDR       ,'I',
  ADDP_OPCODE_SUBMASK      ,'I',
  ADDP_OPCODE_NETNAME      ,'S',
  ADDP_OPCODE_DOMAIN       ,'S',
  ADDP_OPCODE_HWTYPE       ,'u',
  ADDP_OPCODE_HWREV        ,'u',
  ADDP_OPCODE_FIRMWARE     ,'S',
  ADDP_OPCODE_RESULTMESSAGE,'S',
  ADDP_OPCODE_RESULTFLAG   ,'-',
  ADDP_OPCODE_GATEWAY      ,'I',
  ADDP_OPCODE_CONFIGERR    ,'-',
  ADDP_OPCODE_HWNAME       ,'S',
  ADDP_OPCODE_REALPORT     ,'u',
  ADDP_OPCODE_DNS          ,'I',
  ADDP_OPCODE_DHCP         ,'-',
  ADDP_OPCODE_ERRCODE      ,'-',
  ADDP_OPCODE_PORT_CNT     ,'u',
  ADDP_OPCODE_SECURE_RP    ,'u',
  ADDP_OPCODE_VERSION      ,'u',
  ADDP_OPCODE_VENDORGUID   ,'-',
  ADDP_OPCODE_UNKNOWN19    ,'u', # 'u' shows as a number. '?' shows as hex. Either work.
);
#print Dumper(\%ADDP_OPCODE_TYPE); die();

my @ADDP_ERROR_CODE=(
  'Success',
  'Authentication Failure',
  'Unit has address',    # from AddpDevice$AddpError.class
  'Invalid Value',
  'Invalid Data',        # from AddpDevice$AddpError.class
  'Unsupported command', # from AddpDevice$AddpError.class
  'Unable to save value',
);

# from addp.h
my @ADDP_WIRELESS_AUTO=(
  'Disabled',
  'Enabled',
);

# These wifi strings might change if we need to match the command line usage of any Digi programs
# from AddpDevice$AddpError.class
my @ADDP_WLAN_ENCMODE=(
  'Unknown',
  'None',
  'WEP40',
  'WEP128', # Where is WPA and WPA2?
);
#print Dumper(\@ADDP_WLAN_ENCMODE); die();

# from AddpDevice$AddpError.class
my @ADDP_WLAN_AUTHMODE=(
  'Unknown',
  'Open System',
  'Shared Key',
  'Open Shared Key',
);
#print Dumper(\@ADDP_WLAN_AUTHMODE); die();

my %ADDP_RESULT_FLAGS=(
  0x00 => 'Success',
  0xFF => 'Failure',
);
#print Dumper(\%ADDP_RESULT_FLAGS);

my @ADDP_CONFIG_ERRORS=(
  'No',
  'Digi in different subnet than sender',
);

my @ADDP_BOOLEAN_FLAGS=(
  'Off',
  'On',
);

# From Metasploit addp.rp.
# Interesting that PortServer II Rack 16 would be defined since it doesn't respond to ADDP
# The PortServer II is why I wrote all the SNMP code.
my @ADDP_HWTYPES=qw/
      unknown ps3_desk8 ps3_desk16 ps3_desk32 ps3_rack16 ps2_desk16 ps2_rack16
      lets_desk1 lets_desk2 lets_desk4 dorpia_dinrail1 nubox01 nubox02 nubox04
      digione_sp digione_ia digione_em
/;
#print Dumper(\@ADDP_HWTYPES); die();

# $arg_bytes: constant width of hex and ascii, often 8
# $arg_data: binary string to dump. "\n" is printed on all but the last line so you can print more.
# $arg_supress: 0 to show printable ascii, 1 to show all as "..." for known binary values where showing ascii would be inappropriate
# Returns nothing.
sub print_hex_dump {
  my ($arg_bytes,$arg_data,$arg_supress)=(@_);
  my $pdh_write;
  while(length($arg_data)) {
    if(length($arg_data) > $arg_bytes) {
      $pdh_write=substr($arg_data,0,$arg_bytes);
      $arg_data=substr($arg_data,$arg_bytes);
    } else {
      $pdh_write=$arg_data;
      $arg_data="";
    }
    printf("%*s ",$arg_bytes*3-1,join(" ",unpack("(H2)*",$pdh_write)));
    if ($arg_supress) {
      $pdh_write='.' x length($pdh_write);
    } else {
      $pdh_write =~ s/[\x00-\x1F\x7F-\xFF]/./g;
    }
    printf("%-*s ",$arg_bytes,$pdh_write);
    print "\n" if (length($arg_data));
  }
}

# returns hex spaced out. DE AD BE EF
# $arg_killspace: The extra space at the end is: 0=put on, 1=left off
sub space_hex {
  my ($arg_bin,$arg_killspace)=(@_);
  my $rv=join(" ",unpack("(H2)*",$arg_bin)); # Should be faster than regex.
  $rv.=" " if (not $arg_killspace);
  return($rv);
}

# $arg_print: 0=don't print just return hash, 1=print like addp, 2=print hex like blog with Perl hash
# $arg_frto: "to" for send, "from" for receive, "command" for command line --addp-decode
# $arg_ip: IP address to or from. May or may not include port number as desired.
# $arg_packet: UDP packet to decode
# Returns %hash of decoded items for response codes.
# Digi addp prints in a prefab order with some forced values. We print in the order found in the packet.
sub addp_decode {
  my ($arg_print,$arg_frto,$arg_ip,$arg_packet)=(@_);
  my %rv;
  my $bytes=8;
  my ($magic,$packettype,$payloadsize,$payload)=unpack("a".ADDP_OPCODE_MAGIC_LEN."nna*",$arg_packet);
  if (not $ADDP_MAGICS{$magic}) {
    print "Not a Digi ADDP packet\n" if ($arg_print);
  } elsif (length($payload) != $payloadsize) {
    print "Damaged Digi ADDP packet\n" if ($arg_print);
  } elsif (not $ADDP_PACKET_NAME{$packettype}) {
    print "Unknown packet type $packettype\n" if ($arg_print);
  } else {
    %rv=(
      $arg_frto  => $arg_ip,
      Magic      => $magic,
      PacketType => $packettype,
    );
    #if ($packettype eq +ADDP_PACKET_DISCOVERY_RESPONSE) {
    #  $rv{$ADDP_OPCODE_FIELD{+ADDP_OPCODE_NETNAME}}=''; # supressed if blank
    #  $rv{$ADDP_OPCODE_FIELD{+ADDP_OPCODE_SECURE_RP}}=0; # not returned for unsupported models
    #}
    if ($arg_print > 1) {
      printf("%*s%s %s\n",$bytes*4+1,"",$arg_frto,$arg_ip);
      print_hex_dump($bytes,$magic                 ,0); printf("Magic %s %s\n",$magic,$ADDP_MAGICS{$magic});
      print_hex_dump($bytes,substr($arg_packet,4,2),1); printf("Packet Type (0x%4.4X) %s\n",$packettype,$ADDP_PACKET_NAME{$packettype});
      print_hex_dump($bytes,substr($arg_packet,6,2),1); printf("Payload Size (%u bytes)\n",$payloadsize);
    } elsif ($arg_print == 1 and $opt_QueryShort==0) {
      printf("%-8s: %s\n",$arg_frto,$arg_ip);
      printf("%-8s: %s %s\n","Magic",$magic,$ADDP_MAGICS{$magic});
      printf("%-8s: %s\n","Type",$ADDP_PACKET_NAME{$packettype});
    }
    # peel leading non tagged fixed fields from packets
    # Included are some captured packets sent from the Digi Device Discovery Tool
    if ($packettype eq +ADDP_PACKET_DISCOVERY_REQUEST) {
# ./addp.pl --debug=1 --decode-addp='44564b540001001cffffffffffff1510bf6db409c83d44a3a36d21797d2f73f914020200'
# ./addp.pl --debug=1 --decode-addp='4449474900010006ffffffffffff'
# ./addp.pl --debug=1 --decode-addp='44564b5400010006ffffffffffff'
# ./addp.pl --debug=1 --decode-addp='4449474900020084010600409d3201260204c0a8326b0304ffffff000b04c0a832010408486f73744e616d6505096d61706c652e68616b0601000d0f506f72745365727665722054532034070100081e56657273696f6e2038323030303734375f57312030322f31362f323031360e04000003031304000004031901010f04c0a8320a100400000001120104'
      my $targetMAC;
      ($targetMAC,$payload)=unpack("a".ADDP_OPCODE_MAC_LEN."a*",$payload);
      my $targetMACn=join(":",unpack("(H2)*",$targetMAC)); $rv{$ADDP_OPCODE_FIELD{+ADDP_OPCODE_MAC}}=$targetMACn;
      if ($arg_print > 1) {
        print_hex_dump($bytes,$targetMAC,1); printf("%s %s\n",$ADDP_OPCODE_FIELD{+ADDP_OPCODE_MAC},$targetMACn);
      } elsif ($arg_print == 1 and $opt_QueryShort==0) {
        printf("%-8s: %s\n",$ADDP_OPCODE_FIELD{+ADDP_OPCODE_MAC},$targetMACn);
      }
    } elsif ($packettype eq +ADDP_PACKET_DHCP_REQUEST) {
# ./addp.pl --debug=1 --decode-addp='44494749000700080100409d32012600'
# ./addp.pl --debug=1 --decode-addp='44494749000800260a01ff091641757468656e7469636174696f6e204661696c757265110101010600409d320126'
# ./addp.pl --debug=1 --decode-addp='444947490007000c0100409d3201260464627073'
# ./addp.pl --debug=1 --decode-addp='44494749000800240a010009144f7065726174696f6e205375636365737366756c110100010600409d320126'
      my $enableDHCP;
      my $targetMAC;
      my $pwlen;
      ($enableDHCP,$targetMAC,$pwlen,$payload)=unpack("aa".ADDP_OPCODE_MAC_LEN."aa*",$payload);
      my $enableDHCPn=hex(unpack("H*",$enableDHCP)); $rv{$ADDP_OPCODE_FIELD{+ADDP_OPCODE_DHCP}}=$enableDHCPn;
      my $targetMACn=join(":",unpack("(H2)*",$targetMAC)); $rv{$ADDP_OPCODE_FIELD{+ADDP_OPCODE_MAC}}=$targetMACn;
      my $pwlenn=hex(unpack("H*",$pwlen));
      my $password;
      ($password,$payload)=unpack("a".$pwlenn."a*",$payload);
      if ($arg_print > 1) {
        print_hex_dump($bytes,$enableDHCP,1); printf("%s %s\n",$enableDHCPn?"Enable":"Disable",$ADDP_OPCODE_FIELD{+ADDP_OPCODE_DHCP});
        print_hex_dump($bytes,$targetMAC,1); printf("%s %s\n",$ADDP_OPCODE_FIELD{+ADDP_OPCODE_MAC},$targetMACn);
        print_hex_dump($bytes,$pwlen,0); printf("Password length %u\n",$pwlenn);
        if ($pwlenn) {
          print_hex_dump($bytes,$password,0); printf("Password %s\n",$password);
        }
      } elsif ($arg_print == 1 and $opt_QueryShort==0) {
        printf("%-8s: %s\n",$ADDP_OPCODE_FIELD{+ADDP_OPCODE_DHCP},$enableDHCPn?"Enable":"Disable");
        printf("%-8s: %s\n",$ADDP_OPCODE_FIELD{+ADDP_OPCODE_MAC},$targetMACn);
        if ($pwlenn) {
          printf("%-8s: %s\n","Password",$password);
        }
      }
    } elsif ($packettype eq +ADDP_PACKET_STATIC_NETCONFIG_REQUEST) {
# ./addp.pl --debug=1 --decode-addp='4449474900030013c0a8326bffffff00c0a8320100409d32012600'
# ./addp.pl --debug=1 --decode-addp='44494749000400260a01ff091641757468656e7469636174696f6e204661696c757265110101010600409d320126'
# ./addp.pl --debug=1 --decode-addp='4449474900030017c0a8326bffffff00c0a8320100409d3201260464627073'
# ./addp.pl --debug=1 --decode-addp='44494749000400240a010009144f7065726174696f6e205375636365737366756c110100010600409d320126'
      #print_hex_dump($bytes,$payload,1); print "***\n";
      my $ipaddr;
      my $submask;
      my $gateway;
      my $targetMAC;
      my $pwlen;
      ($ipaddr,$submask,$gateway,$targetMAC,$pwlen,$payload)=unpack("a".ADDP_OPCODE_IPADDR_LEN."a".ADDP_OPCODE_SUBMASK_LEN."a".ADDP_OPCODE_GATEWAY_LEN."a".ADDP_OPCODE_MAC_LEN."aa*",$payload);
      my $ipaddrn=inet_ntoa($ipaddr); $rv{$ADDP_OPCODE_FIELD{+ADDP_OPCODE_IPADDR}}=$ipaddrn;
      my $submaskn=inet_ntoa($submask); $rv{$ADDP_OPCODE_FIELD{+ADDP_OPCODE_SUBMASK}}=$submaskn;
      my $gatewayn=inet_ntoa($gateway); $rv{$ADDP_OPCODE_FIELD{+ADDP_OPCODE_GATEWAY}}=$gatewayn;
      my $targetMACn=join(":",unpack("(H2)*",$targetMAC)); $rv{$ADDP_OPCODE_FIELD{+ADDP_OPCODE_MAC}}=$targetMACn;
      my $pwlenn=hex(unpack("H*",$pwlen));
      my $password;
      ($password,$payload)=unpack("a".$pwlenn."a*",$payload);
      if ($arg_print > 1) {
        print_hex_dump($bytes,$ipaddr,1); printf("%s %s\n",$ADDP_OPCODE_FIELD{+ADDP_OPCODE_IPADDR},$ipaddrn);
        print_hex_dump($bytes,$submask,1); printf("%s %s\n",$ADDP_OPCODE_FIELD{+ADDP_OPCODE_SUBMASK},$submaskn);
        print_hex_dump($bytes,$gateway,1); printf("%s %s\n",$ADDP_OPCODE_FIELD{+ADDP_OPCODE_GATEWAY},$gatewayn);
        print_hex_dump($bytes,$targetMAC,1); printf("%s %s\n",$ADDP_OPCODE_FIELD{+ADDP_OPCODE_MAC},$targetMACn);
        print_hex_dump($bytes,$pwlen,0); printf("Password length %u\n",$pwlenn);
        if ($pwlenn) {
          print_hex_dump($bytes,$password,0); printf("Password %s\n",$password);
        }
      } elsif ($arg_print == 1 and $opt_QueryShort==0) {
        printf("%-8s: %s\n",$ADDP_OPCODE_FIELD{+ADDP_OPCODE_IPADDR},$ipaddrn);
        printf("%-8s: %s\n",$ADDP_OPCODE_FIELD{+ADDP_OPCODE_SUBMASK},$submaskn);
        printf("%-8s: %s\n",$ADDP_OPCODE_FIELD{+ADDP_OPCODE_GATEWAY},$gatewayn);
        printf("%-8s: %s\n",$ADDP_OPCODE_FIELD{+ADDP_OPCODE_MAC},$targetMACn);
        if ($pwlenn) {
          printf("%-8s: %s\n","Password",$password);
        }
      }
    } elsif ($packettype eq +ADDP_PACKET_REBOOT_REQUEST) {
# ./addp.pl --debug=1 --decode-addp='444947490005000700409d8928ab00'
# ./addp.pl --debug=1 --decode-addp='44494749000600260a01ff091641757468656e7469636174696f6e204661696c757265110101010600409d8928ab'
# ./addp.pl --debug=1 --decode-addp='444947490005000b00409d8928ab0464627073'
# ./addp.pl --debug=1 --decode-addp='44494749000600240a010009144f7065726174696f6e205375636365737366756c110100010600409d8928ab'
      #print_hex_dump($bytes,$payload,1); print "***\n";
      my $targetMAC;
      my $pwlen;
      ($targetMAC,$pwlen,$payload)=unpack("a".ADDP_OPCODE_MAC_LEN."aa*",$payload);
      my $targetMACn=join(":",unpack("(H2)*",$targetMAC)); $rv{$ADDP_OPCODE_FIELD{+ADDP_OPCODE_MAC}}=$targetMACn;
      my $pwlenn=hex(unpack("H*",$pwlen));
      my $password; # I don't want the password in the returned hash.
      ($password,$payload)=unpack("a".$pwlenn."a*",$payload);
      if ($arg_print > 1) {
        print_hex_dump($bytes,$targetMAC,1); printf("%s %s\n",$ADDP_OPCODE_FIELD{+ADDP_OPCODE_MAC},$targetMACn);
        print_hex_dump($bytes,$pwlen,0); printf("Password length %u\n",$pwlenn);
        if ($pwlenn) {
          print_hex_dump($bytes,$password,0); printf("Password %s\n",$password);
        }
      } elsif ($arg_print == 1 and $opt_QueryShort==0) {
        printf("%-8s: %s\n",$ADDP_OPCODE_FIELD{+ADDP_OPCODE_MAC},$targetMACn);
        if ($pwlenn) {
          printf("%-8s: %s\n","Password",$password);
        }
      }
    }
    # See examples above for responses.
    if (length($payload)) {
      while(length($payload)) {
        my ($opcode,$datalen)=unpack("CC",$payload);
        my $optext=$ADDP_OPCODE_FIELD{$opcode};
        my $optype=$ADDP_OPCODE_TYPE{$opcode};
        my $data=substr($payload,2,$datalen);
        my $datafmt='?';
        my $dataresult;
        my $supress=1;
        if ($optype eq 'M') {
          $datafmt=join(":",unpack("(H2)*",$data));
        } elsif ($optype eq '?') {
          $datafmt="0x".unpack("(H2)*",$data);
        } elsif ($optype eq 'I') {
          $datafmt=join(".",unpack("C*",$data));
        } elsif ($optype eq 'S') {
          $datafmt=$data;
          $supress=0;
        } elsif ($opcode eq +ADDP_OPCODE_HWTYPE) {
          $dataresult=hex(unpack("H*",$data));
          $datafmt=sprintf("%u-%s",$dataresult,$ADDP_HWTYPES[$dataresult]);
        } elsif ($optype eq 'u') {
          $dataresult=hex(unpack("H*",$data));
          $datafmt=sprintf("%u",$dataresult); # I can't find a better way to convert variable width binary to decimal.
        } elsif ($opcode eq +ADDP_OPCODE_DHCP) {
          $dataresult=hex(unpack("H*",$data));
          $datafmt=sprintf("%u-%s",$dataresult,$ADDP_BOOLEAN_FLAGS[$dataresult]);
        } elsif ($opcode eq +ADDP_OPCODE_CONFIGERR) {
          my $val=hex(unpack("H*",$data));
          $datafmt=sprintf("%u-%s",$val,$ADDP_CONFIG_ERRORS[$val]);
          print "**** The following unit is MIS-CONFIGURED ****\n" if ($arg_print and $packettype eq +ADDP_PACKET_DISCOVERY_RESPONSE);
        } elsif ($opcode eq +ADDP_OPCODE_RESULTFLAG) {
          my $val=hex(unpack("H*",$data));
          $datafmt=sprintf("%u-%s",$val,$ADDP_RESULT_FLAGS{$val});
          $dataresult=$val;
        } elsif ($opcode eq +ADDP_OPCODE_ERRCODE) {
          my $val=hex(unpack("H*",$data));
          $datafmt=sprintf("%u-%s",$val,$ADDP_ERROR_CODE[$val]);
          $dataresult=$val;
        } elsif ($opcode eq +ADDP_OPCODE_VENDORGUID) {
          $datafmt=join("-",unpack("H8H4H4H4H*",$data));
        }
        if ($arg_print and (not $opt_QueryShort or $arg_print >= 2)) {
          if ($arg_print > 1) {
            print_hex_dump($bytes,substr($payload,0,$datalen+2),$supress);
            printf("%u: %s %s\n",$opcode,$optext,$datafmt);
          } elsif ($datafmt eq '?') {
            printf("Unknown Opcode %u with len = %u\n",$opcode,$datalen);
          } else {
            printf("%-8s: %s\n",$optext,$datafmt);
          }
        }
        $rv{$optext}=$datafmt if ($datafmt ne '?');
        $rv{$optext}=$dataresult if (defined $dataresult);
        $payload=substr($payload,2+$datalen);
      }
      if ($packettype eq +ADDP_PACKET_DISCOVERY_RESPONSE and $arg_print and $opt_QueryShort) {
        # These fields need to be parsable with bash read -ra. I'd rather get rid of the spaces than use visually unappealing delimiters.
        my $hwname=$rv{$ADDP_OPCODE_FIELD{+ADDP_OPCODE_HWNAME}};
        $hwname =~ s/\s/_/g;
        my $netname=$rv{$ADDP_OPCODE_FIELD{+ADDP_OPCODE_NETNAME}};
        $netname //= '';
        $netname =~ s/\s/_/g;
        printf("%s%-15s %2u %s %-15s %s %s"
          ,((defined $rv{$ADDP_OPCODE_FIELD{+ADDP_OPCODE_CONFIGERR}} and $rv{$ADDP_OPCODE_FIELD{+ADDP_OPCODE_CONFIGERR}})?"*":"")
          ,$rv{$ADDP_OPCODE_FIELD{+ADDP_OPCODE_IPADDR}}
          ,$rv{$ADDP_OPCODE_FIELD{+ADDP_OPCODE_PORT_CNT}}
          ,$rv{$ADDP_OPCODE_FIELD{+ADDP_OPCODE_SECURE_RP}}?'Y':'N'
          ,$rv{$ADDP_OPCODE_FIELD{+ADDP_OPCODE_MAC}}
          ,$hwname
          ,$netname);
      }
    }
    print "\n" if ($arg_print);
  }
  print Dumper(\%rv) if ($arg_print > 2);
  return %rv;
}

# $arg_heading: addp or snmp
# $arg_frto: "to" for send or "from" for receive
# $arg_ip: destination:port or source ip
# $arg_line: binary data
my $fh_DataDump;
sub dataDump {
  my ($arg_heading,$arg_frto,$arg_ip,$arg_line)=(@_);
  if (not defined $fh_DataDump) {
    my $fh;
    open($fh, '>', $opt_DataDump) or die();
    $fh_DataDump=$fh;
    print $fh "# A Digi ADDP dump by ",$g_src,"\n";
  }
  # Hex packing these lines allows them to be posted online or sent through email not as attachments.
  # Unwanted wrapping is easy to fix and files can be hand edited to include only the necessary lines.
  print $fh_DataDump $arg_heading,",",$arg_frto,",",$arg_ip,",",space_hex($arg_line,1),"\n";
}

# Net::SNMP and net-snmp are broken. They won't allow us to broadcast. We'll implement a v1 broadcast manually.
# I was going to just send junk to get the address but after writing all the code to learn how SNMP works
# it was easier to do it all ourselves without Net::SNMP
# http://www.rane.com/note161.html SNMP: Simple? Network Management Protocol

# $1: OID in text form "1.3.6.1.4.1.2680.1.2.7.3.2.0"
# Returns binary bytes BER encoded or blank if the OID text is invalid
# The object identifier 0x06 and length are not included on the front
sub snmp_oid_encode {
  no integer; # affects >> and &
  my ($arg_oid)=(@_);
  if ($arg_oid =~ m/^\./ || $arg_oid =~ m/\.$/ || $arg_oid =~ m/\.\./ ) {
    return '' if ($opt_Debug == 0);
    print STDERR ("Silly programmer, can't start, end, or contain multiple dots $arg_oid\n");
    die("Just because iReasoning shows it, doesn't make it right!\n");
  }
  my @oida=split(/\./,$arg_oid);
  return '' if (scalar @oida < 3);
  foreach (@oida) {
    return '' if (not $_ =~ m/^[0-9]+$/);
  }
  my $p1=shift(@oida);
  my $p2=shift(@oida);
  return '' if ($p2 > 39);
  $p1 = 40*$p1 + $p2;
  return '' if ($p1 > 127); # So far as I can tell, the first byte cannot be multi byte encoded.
  my $rv=pack("C",$p1);
  foreach(@oida) {
    my $oiv='';
    my $hibit=0x00;
    do {
      $oiv=pack("C",($_ & 0x7F) | $hibit).$oiv;
      $_ >>= 7;
      $hibit=0x80;
    } while($_);
    $rv.=$oiv;
  }
  return $rv;
}
#my $z=unpack("H*",snmp_oid_encode("1.3.6.1.4.1.2680.1.2.7.3.2.0")); $z =~ s/(..)/$1 /g; print $z; die();

# $1 OID in hex form "\x43"
# Returns text dotted notation "1.3" or '' if the binary is invalid
sub snmp_oid_decode {
  no integer;
  my ($arg_oid)=(@_);
  my $rv='';
  if (length($arg_oid)) {
    ($_,$arg_oid)=unpack("Ca*",$arg_oid); # I don't char who you are, that's Perl right there!
    $rv .= int($_/40).".".$_%40;
    my $accum=0;
    while (length($arg_oid)) {
      ($_,$arg_oid)=unpack("Ca*",$arg_oid); # don't need to "use bytes;"
      $accum=($accum << 7) | ($_ & 0x7F); # + also works
      if ($_ < 0x80) {
        $rv .= '.'.$accum;
        $accum=0;
      } elsif (length($arg_oid)==0) {
        $rv='';
        last;
      }
    }
  }
  return $rv;
}
#print snmp_oid_decode(snmp_oid_encode("1.3.6.1.4.1.2680.1.2.7.3.2.0")."\xFF"),"\n"; die();
#my $t1="1.3.6.1.4.1.2680.1.2.7.3.2.0"; my $t2=snmp_oid_decode(snmp_oid_encode($t1)); print $t1,"\n",$t2,"\n",($t1 eq $t2)?"pass":"fail","\n"; die();

# https://en.wikipedia.org/wiki/X.690#Length_octets
# BER length encoding is not the same as for OID above. The description is hard to understand so I'll show by example.
# 0x00 - 0x7F, this byte is length, stores values 0-127
# 0x80 - Variable length with terminator, not implemented here and probably not useful. Who's going to need more than 0x7E (126) bytes? 2.7e+303 ought to be enough for anybody!
# 0x81 - 0xFE, next &=0x7F bytes are length in network byte order. Not sure why this wasn't limited to 1,2,4. A 256**4=4 gibibyte packet is pretty large.
#   Common length specifiers:
#   0x81 - next 1 byte is length, stores values 0-255, best used for values 128-255
#   0x82 - next 2 bytes are length, stores values 0-65535, best used for values 256-65535
#   0x84 - next 4 bytes are length, senders are unlikely to use this since UDP packets can't be large enough to exceed 2 bytes
#   Examples:
#   0x10 - length 0x10 or 16 bytes
#   0x7E - length 0x7E or 126 bytes
#   0x81 0xA0 - length is 0xA0 or 160 bytes
#   0x82 0x00 0xC8 - length is 0x00C8 or 200 bytes. This wastes a byte and should have been encoded as 0x81 0xC8.
#   0x82 0x02 0x2A - length is 0x022A or 554 bytes
# 0xFF - reserved for future use.
sub snmp_encode_length {
  my ($len)=(@_);
  if ($len>=0) {
    return pack("C",$len) if ($len<=127);
    return pack("CC",0x81,$len) if ($len<=255);
    return pack("Cn",0x82,$len) if ($len<=65535);
    #return pack("CN",0x84,$len);
  }
  die("snmp_encode_length can't encode $len\n");
}

my $SNMP_VARBIND_NULL=pack("CC",5,0);
sub snmp_oid_GetRequest {
  my ($arg_community,$arg_oid)=(@_);
  my $rv=snmp_oid_encode($arg_oid);
  $rv = pack("C",0x06).snmp_encode_length(length($rv)).$rv.$SNMP_VARBIND_NULL;
  $rv = pack("C",0x30).snmp_encode_length(length($rv)).$rv;
  $rv = pack("C",0x30).snmp_encode_length(length($rv)).$rv;
  my
  $id = pack("C",0x00); $rv = pack("C",0x02).snmp_encode_length(length($id)).$id.$rv; # Error Index
  $id = pack("C",0x00); $rv = pack("C",0x02).snmp_encode_length(length($id)).$id.$rv; # Error
  $id = pack("C",0x00); $rv = pack("C",0x02).snmp_encode_length(length($id)).$id.$rv; # Request ID
  $rv = pack("C",0xA0).snmp_encode_length(length($rv)).$rv; # GetRequest
  $rv = pack("C",0x04).snmp_encode_length(length($arg_community)).$arg_community.$rv;
  $id = pack("C",0x00); $rv = pack("C",0x02).snmp_encode_length(length($id)).$id.$rv; # Version
  $rv = pack("C",0x30).snmp_encode_length(length($rv)).$rv;
  $rv .= chr(0x00) x 20; # Not sure why Digi sddp is adding this garbage at the end. At least it helps test the code.
  return $rv;
}
#my $z=unpack("H*",snmp_oid_GetRequest("private","1.3.6.1.4.1.2680.1.2.7.3.2.0")); $z =~ s/(..)/$1 /g; print $z; die();

# Output formatted text as shown here.
# http://stackoverflow.com/questions/22998212/decode-snmp-pdus-where-to-start
# $arg_level:  Always call with zero or you'll have trouble
# $arg_indent: Usually 0 but can call with any indent you like.
# $arg_snmp:   binary bytes
# $arg_view:   0=show nothing, 1=show retrieved items, 2=show #1 and hex, 3=show #2 and more debugging messages
# $arg_rv:     always call with {} or {From=>$ip}. You can prefill with other values if you like.
# Returns $arg_rv amended with items found in SNMP. Because of recursion this is used and returned as a hash reference. $arg_rv->{'From'}
sub snmp_decode_recur {
  no integer;
  my ($arg_level,$arg_indent,$arg_snmp,$arg_print,$arg_rv)=(@_);
  my $opcode;
  my $val;
  my $valb;
  my $len; # I tried to use $_ for this but it turns out to be a global. sub functions affect it.
  my $lenbin;
  my $lentitle;
  my $sequence=0;
  my $seqtitle;
  while(length($arg_snmp)) {
    undef $val;
    undef $valb;
    $seqtitle='???';
    $len=0; # snmp_decode_length, see snmp_encode_length for method
    ($opcode,$lenbin,$arg_snmp)=unpack("Caa*",$arg_snmp);
    $len=unpack("C",$lenbin);
    $lentitle="Definite, short";
    if ($len & 0x80) {
      if ($len == 0x80) {
        die("snmp_decode_recur: Variable form not supported yet. Need an example\n");
      }
      if ($len == 0xFF) {
        die("snmp_decode_recur: Reserved form not supported yet. Need an example\n");
      }
      $len &= 0x7F;
      $lentitle=sprintf("Definite, long %u",$len);
      ($len,$arg_snmp)=unpack("a".$len."a*",$arg_snmp);
      $lenbin.=$len;
      $len=hex(unpack("H*",$len));
    }
    if ($arg_print >= 3 and length($lenbin) > (my $fixlen=length(my $fixlenbin=snmp_encode_length($len))) ) {
      printf("Warning: Length bytes could have been encoded in only %u bytes as %s\n",$fixlen,space_hex($fixlenbin,0));
    }
    $sequence++;
    if ($len > length($arg_snmp) and $arg_print >= 1) { # This is an emergency message that shouldn't normally be printed
      printf("Length %s beyond string length of %u\n",$len,length($arg_snmp));
      $arg_snmp='';
    } elsif ($opcode == 0x00) {
      printf("%*s%2.2X %s\n%*sEnd of data length %u\n",$arg_indent,'',$opcode,space_hex($lenbin.$arg_snmp,0),$arg_indent,'',2+length($arg_snmp)) if ($arg_print >= 3);
      $arg_snmp='';
    } elsif ($opcode == 0x30) {
      if ($arg_level == 0 and $arg_print >= 3 and $len < length($arg_snmp) and (substr($arg_snmp,$len,1) cmp 0x00) != 0 ) {
        printf("Warning: First 0x30 sequence length %u does not use entire SNMP string length %u\n",$len,length($arg_snmp));
      }
      if ($arg_level==0) {
        $seqtitle='SNMP Message';
      } elsif ($arg_level==2) {
        $seqtitle='Varbind List';
      } elsif ($arg_level==3) {
        $seqtitle='Varbind';
      }
      ($valb,$arg_snmp)=unpack("a".$len."a*",$arg_snmp);
      printf("%*s%2.2X %s%s length %u (%s) %s\n",$arg_indent,'',$opcode,space_hex($lenbin,0),'Sequence',$len,$lentitle,$seqtitle) if ($arg_print >= 2);
      snmp_decode_recur($arg_level+1,$arg_indent+3,$valb,$arg_print,$arg_rv);
    } elsif ($opcode == 0x02) {
      if ($arg_level==1) {
        if ($sequence==1) {
          $seqtitle='SNMP Version';
        }
      } elsif ($arg_level==2) {
        if ($sequence==1) {
          $seqtitle='Request ID';
        } elsif ($sequence==2) {
          $seqtitle='Error';
        } elsif ($sequence==3) {
          $seqtitle='Error Index';
        }
      } elsif ($arg_level==4) {
        $seqtitle='Value';
      }
      ($valb,$arg_snmp)=unpack("a".$len."a*",$arg_snmp);
      $val=hex(unpack("H*",$valb));
      printf("%*s%2.2X %s%s%s length %u (%s) val %u %s\n",$arg_indent,'',$opcode,space_hex($lenbin,0),space_hex($valb,0),'Integer',$len,$lentitle,$val,$seqtitle) if ($arg_print >= 2);
    } elsif ($opcode == 0x04) {
      if ($arg_level==1) {
        $seqtitle='SNMP Community';
      } elsif ($arg_level==4) {
        if ($sequence==1) {
          $seqtitle='Object Identifier';
        } elsif ($sequence==2) {
          $seqtitle='Value';
        }
      }
      ($valb,$arg_snmp)=unpack("a".$len."a*",$arg_snmp);
      printf("%*s%2.2X %s%s\n%*s%s length %u (%s) '%s' %s\n",$arg_indent,'',$opcode,space_hex($lenbin,0),space_hex($valb,0),$arg_indent,'','Octet',$len,$lentitle,$valb,$seqtitle) if ($arg_print >= 2);
      $val=$valb;
    } elsif ($opcode == 0x05) {
      $seqtitle='NULL';
      ($valb,$arg_snmp)=unpack("a".$len."a*",$arg_snmp);
      printf("%*s%2.2X %s%s%s length %u (%s) %s\n",$arg_indent,'',$opcode,space_hex($lenbin,0),space_hex($valb,0),'Null',$len,$lentitle,$seqtitle) if ($arg_print >= 2);
    } elsif ($opcode == 0x06) {
      $seqtitle='Object Identifier';
      ($valb,$arg_snmp)=unpack("a".$len."a*",$arg_snmp);
      $val=snmp_oid_decode($valb);
      printf("%*s%2.2X %s%s%s length %u (%s) val %s %s\n",$arg_indent,'',$opcode,space_hex($lenbin,0),space_hex($valb,0),'ObjID',$len,$lentitle,$val,$seqtitle) if ($arg_print >= 2);
    } elsif ($opcode == 0xA0) {
      $seqtitle='SNMP PDU GetRequest';
      ($valb,$arg_snmp)=unpack("a".$len."a*",$arg_snmp);
      printf("%*s%2.2X %s%s length %u (%s) %s\n",$arg_indent,'',$opcode,space_hex($lenbin,0),'GetReq',$len,$lentitle,$seqtitle) if ($arg_print >= 2);
      snmp_decode_recur($arg_level+1,$arg_indent+3,$valb,$arg_print,$arg_rv);
    } elsif ($opcode == 0xA2) {
      $seqtitle='SNMP PDU GetResponse';
      ($valb,$arg_snmp)=unpack("a".$len."a*",$arg_snmp);
      printf("%*s%2.2X %s%s length %u (%s) %s\n",$arg_indent,'',$opcode,space_hex($lenbin,0),'GetRes',$len,$lentitle,$seqtitle) if ($arg_print >= 2);
      snmp_decode_recur($arg_level+1,$arg_indent+3,$valb,$arg_print,$arg_rv);
    } elsif ($opcode == 0xA3) { # 0xA3 hasn't been tested
      $seqtitle='SNMP PDU SetRequest';
      ($valb,$arg_snmp)=unpack("a".$len."a*",$arg_snmp);
      printf("%*s%2.2X %s%s length %u (%s) %s\n",$arg_indent,'',$opcode,space_hex($lenbin,0),'SetReq',$len,$lentitle,$seqtitle) if ($arg_print >= 2);
      snmp_decode_recur($arg_level+1,$arg_indent+3,$valb,$arg_print,$arg_rv);
    } else {
      ($valb,$arg_snmp)=unpack("a".$len."a*",$arg_snmp);
      printf("%*s/%2.2X %s%s%s length %u (%s)\n",$arg_indent-1,'',$opcode,space_hex($lenbin,0),space_hex($valb,0),'Unknown',$len,$lentitle) if ($arg_print >= 2);
    }
    if (defined $val and $seqtitle ne '???') {
      $arg_rv->{$seqtitle}=$val;
    }
  }
  print Dumper($arg_rv) if ($arg_level == 0 and $arg_print);
  return $arg_rv; # This is a hash reference.
}
#snmp_decode_recur(0,0,snmp_oid_GetRequest("private","1.3.6.1.4.1.2680.1.2.7.3.2.0"),3,{}); die();

my %SNMP_LIST=(
# We can't use ADDR_OPCODE on the ones that are different and shouldn't on the ones that require special handling.
"1.3.6.1.2.1.1.1.0",              ,"Name",     # Name, only used for lookup. This is sent broadcast.
"1.3.6.1.2.1.2.2.1.6.1"           ,$ADDP_OPCODE_FIELD{+ADDP_OPCODE_MAC},      # ifPhysAddress, MAC, generic
"1.3.6.1.2.1.1.5.0"               ,"NetName",  # sysName.0, Network Name, generic
"1.3.6.1.4.1.332.11.5.3.3.20.19.0","NetName2",
#"1.3.6.1.2.1.10.33.1.0"           ,$ADDP_OPCODE_FIELD{+ADDP_OPCODE_PORT_CNT},   # rs232Number.0, Port Count, PortServer TS, PortServer II
"1.3.6.1.2.1.19.1.0"              ,$ADDP_OPCODE_FIELD{+ADDP_OPCODE_PORT_CNT},    # charNumber.0, Port Count, PortServer TS, PortServer II
"1.3.6.1.4.1.332.11.5.3.3.20.31.0",$ADDP_OPCODE_FIELD{+ADDP_OPCODE_SECURE_RP}, # RealPort SSL Port Number
"1.3.6.1.4.1.332.11.5.3.3.20.11.0","-Name1",   # Product Name part 1, PortServer TS, not PortServer II
"1.3.6.1.4.1.332.11.5.3.3.20.12.0","-Name2",   # Product Name part 2, PortServer TS, not PortServer II
);
my %SNMP_LIST_TOGET=(%SNMP_LIST);
delete $SNMP_LIST_TOGET{"1.3.6.1.2.1.1.1.0"};
# assemble all of the SNMP return packets into a single hash.
# $arg_snmplist: array of arrays of received SNMP packets as produced by addp_broadcst
# $arg_print: see snmp_decode_recur
# $arg_addpfound: hash ref of IP already found by ADDP. SNMP responses already found will not be shown. They are returned in the hash.
# $arg_dump: 0=to supress debug stuff for normal display, 1 to show all debug items as part of a --data-read debug dump
# Returns the assembled data as hash
sub snmp_assemble {
  my ($arg_snmplist,$arg_print,$arg_addpfound,$arg_dump)=(@_);
  my %rv;
  my $ar;
  print "SNMP Responses:\n" if ($arg_dump or $arg_print >= 2 or ($arg_print==1 and not $opt_QueryShort));
  foreach $ar (@$arg_snmplist) {
    my $from=inet_ntoa($ar->[0]);
    my $hr;
    if ($arg_print >= 3) {
      my $from=inet_ntoa($ar->[0]);
      print "From ",$from,"\n";
      $hr=snmp_decode_recur(0,0,$ar->[1],$arg_print,{From=>$from});
      print "\n";
    } else {
      $hr=snmp_decode_recur(0,0,$ar->[1],0         ,{From=>$from});
    }
    my $oid=$hr->{'Object Identifier'};
    my $field=$SNMP_LIST{$oid}; # translate OID to field name.
    my $val=$hr->{'Value'};
    if (defined $val and defined $field) { # just in case some hacker decides to push me some non solicited packets
      my $addr=$hr->{'From'};
      if ($field eq "MAC") {
        $val=join(":",unpack("(H2)*",$val));
      } elsif ($field eq 'Name') {
        my $newval=$val;
        $newval =~ s/\bDigi\b//gi ;          # Digi International PortServer II v3.1.13 Nov  1 2006
        $newval =~ s/\bInternational\b//gi ; # PortServer TS 2 Version 82000747_W1 02/16/2016
        if ($val ne $newval or $newval =~ m/\bPortServer\b/i ) {
          $newval =~ s/\bVersion.*$//gi ;
          $newval =~ s/\bv[0-9].*$//g ;
          $newval =~ s/\s{2,}/ /g ;       # because it was too hard to clean the right number of spaces
          $newval =~ s/^\s+//g ;
          $newval =~ s/\s+$//g ;
          $rv{$addr}{'SNMPName'}=$val;
          $val=$newval;
        }
      }
      #print $field," ",$addr," ",$val,"\n";
      $rv{$addr}{$field}=$val;
    }
  }
  undef $ar;
  my $addr;
  my $hs;
  foreach $addr (sort keys %rv) {
    $hs=$rv{$addr};
    #print $addr," ",Dumper($hs);
    # The --data-read dumps include all broadcast responses. MAC is one of the UC requests.
    # It's important that we leave those in because people will want more models supported and that string is what is needed to add detection.
    if ($hs->{$ADDP_OPCODE_FIELD{+ADDP_OPCODE_MAC}} and ($arg_print >= 2 or $arg_dump or ($arg_print==1 and not $opt_QueryShort) or ($opt_QueryShort and not %$arg_addpfound{$addr}))) {
      if ($hs->{'-Name1'} and $hs->{'-Name2'}) {
        $hs->{'SNMPName'}=$hs->{'Name'};
        $hs->{'Name'}=$hs->{'-Name1'}." ".$hs->{'-Name2'};
        #delete $hs->{'-Name1'};
        #delete $hs->{'-Name2'};
      }
      $hs->{'NetName'}=$hs->{'NetName2'} if (not $hs->{'NetName'} and $hs->{'NetName2'});
      $hs->{'NetName'}='' if (not $hs->{'NetName'});
      my $hwname=$hs->{'Name'};
      $hwname =~ s/\s/_/g;
      printf("%-15s %2u %s %-15s %s %s\n",$addr,$hs->{$ADDP_OPCODE_FIELD{+ADDP_OPCODE_PORT_CNT}},$hs->{$ADDP_OPCODE_FIELD{+ADDP_OPCODE_SECURE_RP}}?'Y':'N',$hs->{$ADDP_OPCODE_FIELD{+ADDP_OPCODE_MAC}},$hwname,$hs->{'NetName'});
    }
  }
  return %rv;
}

# Send addp multicast or --addpip unicast. When searching -Q, also send snmp broadcast and snmp unicast
# $arg_print: 0=don't print, 1=print like addp, 2=print debug, 3=print #2 plus Perl hashes, 4=#3 plus debug lines, 5=#4 plus way too many debug lines
#   Generally $arg_print = $opt_Debug + 1
#   +1 for SNMP debug level because SNMP has a lot more traffic.
# $arg_responses: 0=get all responses for 2 seconds, n=stop after n responses
#   usually specify 0 for general discovery, 1 for any targeted command. So far all targeted commands only return one response.
# Returns array of addp responses. Each response is hex bytes only. You need to call addp_decode to read them.
#   SNMP responses are only printed on request. Nothing SNMP is returned.
sub addp_broadcast {
  my ($arg_packettype,$arg_addppayload,$arg_print,$arg_responses,$arg_addp,$arg_snmp) = (@_);

  # Each handle has a queue (array) of things to send, an array of things received, and a name for printing debug
  # The hashes store these by handle so the network packet manager can keep all the reads and writes in the right queues.
  # array of received items [[IP,DATA]...], from port has no use so is discarded
  my @rxsnmpbrlist=();
  my @rxsnmpuclist=(); # SNMP broadcasts get pushed onto this list when sent. They are as good of returns as any.
  my @rxaddplist=();
  if ($arg_addp or $arg_snmp) {
    my $rxselect=IO::Select->new(); # rx and tx are the same sockets. rx is always all of them because we neither know nor care which ones still have data to come down
    my $txselect=IO::Select->new(); # tx only contains sockets that have data queued to write

    my %hashdebug;    # names{handle} for screen debugging
    my %hashdump;     # shorter names{handle} for dataDump
    my %rxhash;       # receive arrays{handle}
    my %txhash;       # send arrays{handle}
    # We run sends/receives of addp multicast, snmp broadcast, and snmp unicast in full duplex for minimum wait time.
    # We could combine the addp multicast and snmp unicast sockets. We don't to let the network stack collate the returns for us.
    my @txaddplist; # [[IP:PORT,DATA],...], # destionation port is required.
    my $txaddr;

    if ($arg_addp) {
      # Multicast is Arch Linux AUR only so I'd rather not use it now that I know how to broadcast and multicast transmit with INET.
      # my $txmulti = new IO::Socket::Multicast (
      #  Proto => 'udp',
      #  Blocking => 1,
      #  Timeout => 2,
      #) || die("cannot create multicast socket!\n");
      # We don't join the group because noone multicasts to us. All return traffic is unicast.
      #$txaddr->mcast_add('224.0.5.128');

      $txaddr = IO::Socket::INET->new(
          Proto     => 'udp',
          Broadcast => 0,
          Blocking  => 1,
          Timeout   => 2,
          LocalAddr => $opt_BindAddress,
        ) || die("cannot create multicast socket!\n");
      $rxselect->add($txaddr);
      $hashdump{$txaddr}='addp';
      $hashdebug{$txaddr}='addp';
      $txhash{$txaddr}=\@txaddplist;
      $rxhash{$txaddr}=\@rxaddplist;
      my $msg;
      if (defined $opt_Vendor and defined $opt_GUID) {
        $msg=$arg_addppayload.pack("CCnCC",ADDP_OPCODE_VERSION,2,$opt_Vendor,ADDP_OPCODE_VENDORGUID,length($opt_GUID)).$opt_GUID;
      } else {
        $msg=$arg_addppayload;
      }
      $msg=$opt_Magic.pack("nn", $arg_packettype,length($msg)).$msg;
      #print unpack("H*",$msg);
      addp_decode($arg_print,"to",$opt_AddpIP.":2362",$msg) if ($arg_print >= 2);

      # my $txcount = $txaddr->mcast_send($msg,'224.0.5.128:2362');
      # my $txcount = $txaddr->send($msg,0,pack_sockaddr_in(2362, inet_aton('224.0.5.128')));
      #print "count=$txcount\n";
      $txselect->add($txaddr) if (scalar @txaddplist == 0);
      push(@txaddplist,[pack_sockaddr_in(2362, inet_aton($opt_AddpIP)),$msg]);
      if ($opt_QueryAll and $opt_Magic eq "DIGI" and not defined $opt_GUID and not defined $opt_Vendor) {
        $msg="DVKT".pack("nn", $arg_packettype,length($arg_addppayload)).$arg_addppayload;
        addp_decode($arg_print,"to",$opt_AddpIP.":2362",$msg) if ($arg_print >= 2);
        push(@txaddplist,[pack_sockaddr_in(2362, inet_aton($opt_AddpIP)),$msg]);
        $msg=$ADDP_GUIDS{'NETSILICON'};
        $msg =~ s/-//g;
        $msg=pack("H*",$msg); # Need to get the actual length
        $msg=$arg_addppayload.pack("CCnCC",ADDP_OPCODE_VERSION,2,512,ADDP_OPCODE_VENDORGUID,length($msg)).$msg;
        $msg="DVKT".pack("nn", $arg_packettype,length($msg)).$msg;
        addp_decode($arg_print,"to",$opt_AddpIP.":2362",$msg) if ($arg_print >= 2);
        push(@txaddplist,[pack_sockaddr_in(2362, inet_aton($opt_AddpIP)),$msg]);
      }
    }

    my @txsnmpbrlist; # [IP_PORT,TEXT]
    my $txsnmpbr;
    my @txsnmpuclist; # [IP_PORT,TEXT]
    my $txsnmpuc;
    if ($arg_snmp and $arg_print) {
      $txsnmpbr = IO::Socket::INET->new(
        Proto     => 'udp',
        Broadcast => 1,
        Blocking  => 1,
        Timeout   => 2,
        LocalAddr => $opt_BindAddress,
        ) or die "Can't bind : $@\n";
      $rxselect->add($txsnmpbr);
      $txhash{$txsnmpbr}=\@txsnmpbrlist;
      $rxhash{$txsnmpbr}=\@rxsnmpbrlist;
      $hashdump{$txsnmpbr}='snmp';
      $hashdebug{$txsnmpbr}='snmpbr';
      my $msg=snmp_oid_GetRequest("public","1.3.6.1.2.1.1.1.0"); # sysDescr.0
      $txselect->add($txsnmpbr) if (scalar @txsnmpbrlist == 0);
      push(@txsnmpbrlist,[pack_sockaddr_in(161, INADDR_BROADCAST),$msg]);
      snmp_decode_recur(0,0,$msg,$arg_print,{From=>'127.0.0.1'}) if ($arg_print >= 3);
      #$txsnmpbr->send(snmp_oid_GetRequest("public","1.3.6.1.2.1.1.1.0"),0,pack_sockaddr_in(161, INADDR_BROADCAST));

      $txsnmpuc = IO::Socket::INET->new(
        Proto     => 'udp',
        Broadcast => 0,
        Blocking  => 1,
        Timeout   => 2,
        LocalAddr => $opt_BindAddress,
        ) or die "Can't bind : $@\n";
      $rxselect->add($txsnmpuc);
      $hashdump{$txsnmpuc}='snmp';
      $hashdebug{$txsnmpuc}='snmpuc';
      $txhash{$txsnmpuc}=\@txsnmpuclist;
      $rxhash{$txsnmpuc}=\@rxsnmpuclist;
      # This socket is used when we get some snmp broadcast responses
    }

    # Network Packet Manager: full duplex management of however many network queues were created above and more that may be added by SNMP responses.
    # new tx entries can be added at any time so long as you maintain $txselect
    my $tmstartdebug=[gettimeofday()]; # An array, not affected by use integer.
    printf STDERR ("*db %f start\n",tv_interval($tmstartdebug, [gettimeofday()])) if ($arg_print >= 4);
    if ($txselect->count()) {
      my $responses=$arg_responses;
      my $msg;
      my $tmstart=$tmstartdebug;
      my @readysocks;
      my $readysock;
      # dump is universal so we can do that here. Doing that here keeps the dumped packets in time order.
      # we don't decode sends because we don't want to add the code to figure out which decoder to call: snmp or addp
      # we don't decode receives because printing them the way we want takes a lot of code.
      do {
        printf STDERR ("*db %f loop-all\n",tv_interval($tmstartdebug, [gettimeofday()])) if ($arg_print >= 5);
        # Ambitious write as many as we can until all sockets block
        while (@readysocks=$txselect->can_write(0)) {
          printf STDERR ("*db %f loop-send\n",tv_interval($tmstartdebug, [gettimeofday()])) if ($arg_print >= 5);
          foreach $readysock (@readysocks) { # I hope can_write doesn't report writable when a only partial UDP packet can be sent
            my $arready=$txhash{$readysock};     # array ref of all items in this ready queue waiting to be sent
            my $arsend=shift(@$arready); # send first item
            $txselect->remove($readysock) if (scalar @$arready == 0); # drop the sender when last item sent
            #print Dumper(\@$arsend);
            my $txcount = $readysock->send(@$arsend[1],0,@$arsend[0]); # send(data,0,ip:port)
            my ($port,$addr)=unpack_sockaddr_in(@$arsend[0]);
            dataDump($hashdump{$readysock},"to",inet_ntoa($addr).":".$port,@$arsend[1]) if (length($opt_DataDump));
            printf STDERR ("*db %f send %-6s to %16s:%u %u bytes\n",tv_interval($tmstartdebug, [gettimeofday()]),$hashdebug{$readysock},inet_ntoa($addr),$port,$txcount) if ($arg_print >= 4);
          }
          if ($txselect->count()==0) {
            my $tmstart=[gettimeofday()]; # Sending the last item extends the wait time
            printf STDERR ("*db %f start time reset\n",tv_interval($tmstartdebug, [gettimeofday()])) if ($arg_print >= 5);
          }
        }
        # Get reponses
        my $wait=($txselect->count())?0.1:$opt_TimeoutS; # not affected by use integer
        printf STDERR ("*db %f wait %f\n",tv_interval($tmstartdebug, [gettimeofday()]),$wait) if ($arg_print >= 5);
        @readysocks=$rxselect->can_read($wait);
        foreach $readysock (@readysocks) {
          my $arready=$rxhash{$readysock}; # array for receive storage
          my $peer = $readysock->recv($msg,1024);
          my ($port,$addr)=unpack_sockaddr_in($peer);
          dataDump($hashdump{$readysock},"from",inet_ntoa($addr).":".$port,$msg) if (length($opt_DataDump));
          printf STDERR ("*db %f recv %-6s fr %16s:%u %u bytes\n",tv_interval($tmstartdebug, [gettimeofday()]),$hashdebug{$readysock},inet_ntoa($addr),$port,length($msg)) if ($arg_print >= 4);
          push(@$arready,[$addr,$msg]);
        }
        # Queue up SNMP unicast requests for additional info from SNMP broadcast returns of interest.
        if (scalar @rxsnmpbrlist) {
          my $ar;
          foreach $ar (@rxsnmpbrlist) {
            my $from=inet_ntoa($ar->[0]);
            my $snmp=snmp_decode_recur(0,0,$ar->[1],0,{From=>$from});
            my $text=lc $snmp->{Value};
            if ($text =~ m/\bdigi\b/ || $text =~ m/\bportserver\b/ ) { # TODO: detect more models
              push (@rxsnmpuclist,$ar); # They all get dumped but we only analyze the ones we care about.
              my $oidtext;
              foreach $oidtext (keys %SNMP_LIST_TOGET) {
                my $msg=snmp_oid_GetRequest("public",$oidtext);
                $txselect->add($txsnmpuc) if (scalar @txsnmpuclist == 0);
                push(@txsnmpuclist,[pack_sockaddr_in(161, $ar->[0]),$msg]);
                #dataDump($hashdump{$txsnmpuc},"qu",inet_ntoa($ar->[0]).":161",$msg) if (length($opt_DataDump));
                printf STDERR ("*db %f queu %-6s to %16s:%u %u bytes %s\n",tv_interval($tmstartdebug, [gettimeofday()]),$hashdebug{$txsnmpuc},$from,161,length($msg),$text) if ($arg_print >= 4);
                snmp_decode_recur(0,0,$msg,$arg_print,{From=>'127.0.0.1'}) if ($arg_print >= 3);
              }
            }
          }
          @rxsnmpbrlist=(); # all were processed or discarded!
        }
      } while(
           $txselect->count()
        or (tv_interval($tmstart, [gettimeofday()])<$opt_TimeoutS and ($arg_responses == 0 or --$responses > 0)) # < chosen over <= to work properly with use integer
      );
    }
    printf STDERR ("*db %f done\n",tv_interval($tmstartdebug, [gettimeofday()])) if ($arg_print >= 4);
    #print Dumper(\@rxaddplist);
    foreach($rxselect->handles()) {
      $rxselect->remove($_);
      $_->close();
    }
  }

  # Show ADDP
  my %addpfound; # includes shown and found so they can be excluded from the SNMP listing
  if ($arg_print) {
    my $ar;
    my $lim=$opt_LimitQuery;
    my $shown=0;
    my $configured=0;
    foreach $ar (@rxaddplist) {
      $addpfound{inet_ntoa($ar->[0])}='1';
      my $ip='';
      if (length($opt_BackingStore)) {
        my %device=addp_decode(0,"from",inet_ntoa($ar->[0]),$ar->[1]);
        $ip=$device{'IP'};
        if (defined $device{'ConfigEr'} and $device{'ConfigEr'}) {
          $ip=''; # Always show misconfigured devices even if they are in the backing store because they are unreachable
        }
      }
      if (length($ip)==0 or not defined $BackingStore{$ip}) {
        if ($opt_LimitQuery==0 or $lim) {
          addp_decode($arg_print,"from",inet_ntoa($ar->[0]),$ar->[1]);
          $shown++;
          $lim-- if ($lim);
        }
      } else {
        $configured++
      }
    }
    if (not scalar @rxaddplist) {
      print "No addp Digi devices found\n";
    } elsif ($configured==scalar @rxaddplist) {
      printf("All of the %u discovered devices are already configured.\n",$configured);
    } else {
      printf("%u already configured devices were not shown\n",$configured) if ($configured);
      if ($shown + $configured < scalar @rxaddplist) {
        printf("%u %sdevices were not shown\n",scalar @rxaddplist-$shown-$configured,length($opt_BackingStore)?"unconfigured ":"discovered ");
      }
    }
  }

  # Show SNMP responses.
  if ($arg_print and scalar @rxsnmpuclist) {
    #print Dumper(\%addpfound);
    my %hsnmp=snmp_assemble(\@rxsnmpuclist,$arg_print,\%addpfound,0);
    print Dumper(\%hsnmp) if ($arg_print and (not $opt_QueryShort or $arg_print > 1));
  }

  return @rxaddplist;
}

sub main {
  my $exitcode=0;
  my $ViewLVL=1+$opt_Debug;
  $ViewLVL=0 if ($opt_Quiet);

  if (($opt_SaveSettings or $opt_RebootDevice) and $opt_AddpIP ne $DefaultAddpIP and length($opt_MACAddress)==0) {
    my @resp=addp_broadcast(+ADDP_PACKET_DISCOVERY_REQUEST,pack("H*",'FF' x 6),($ViewLVL>1)?$ViewLVL:0,1,1,0);
    $exitcode=(scalar @resp)?0:1;
    foreach(@resp) {
      my %resp=addp_decode(0,"from",inet_ntoa($_->[0]),$_->[1]); # probably destroys $_
      my $mac=$resp{$ADDP_OPCODE_FIELD{+ADDP_OPCODE_MAC}};
      if ($mac and not isNotValidMAC($mac,0)) {
        $opt_MACAddress=$mac;
        printf("Retrieved MAC %s from %s\n",$opt_MACAddress,$opt_AddpIP);
        optclean_MAC();
      }
    }
    if (length($opt_MACAddress)==0) {
      printf STDERR ("Unable to retrieve MAC for %s\n",$opt_AddpIP);
    }
  }

  if ($opt_QueryAll) {
    $exitcode=addp_broadcast(+ADDP_PACKET_DISCOVERY_REQUEST,pack("H*",'FF' x 6),$ViewLVL,$opt_AddpIP ne $DefaultAddpIP,1,$opt_SNMP)?0:1;
  }

  if ($opt_QueryMAC and length($opt_MACAddress)) {
    print "MAC",lc $opt_MACAddress,"\n";
    $exitcode=addp_broadcast(+ADDP_PACKET_DISCOVERY_REQUEST,pack("H*",$opt_MACAddress),$ViewLVL, lc $opt_MACAddress ne 'ffffffffffff',1,0 )?0:1;
  }

  if ($opt_SaveSettings) { # Set IP address, static or DHCP
    if ($exitcode or length($opt_MACAddress)==0) {
      print "Settings request skipped due to failed previous operation\n"
    } else {
      my $packettype;
      my $payload;
      if (defined $opt_DHCP) {
        my $dhcp=(lc $opt_DHCP eq 'off')?0:1;
        $packettype=+ADDP_PACKET_DHCP_REQUEST;
        $payload=pack("C",$dhcp);
      } else {
        $packettype=+ADDP_PACKET_STATIC_NETCONFIG_REQUEST;
        $payload=pack("a".ADDP_OPCODE_IPADDR_LEN."a".ADDP_OPCODE_SUBMASK_LEN."a".ADDP_OPCODE_GATEWAY_LEN,inet_aton($opt_IPAddress),inet_aton($opt_IPSubnet),inet_aton($opt_IPGateway));
      }
      $payload .= pack("H*",$opt_MACAddress).pack("C",length($opt_Password)).$opt_Password ; # blank password is not supressed. If it were we couldn't put the GUID on the end
      my @resp=addp_broadcast($packettype,$payload,$ViewLVL,1,1,0);
      $exitcode = (scalar @resp)?0:1;
      foreach(@resp) {
        my %resp=addp_decode(0,"from",inet_ntoa($_->[0]),$_->[1]); # probably destroys $_
        if ($resp{$ADDP_OPCODE_FIELD{+ADDP_OPCODE_RESULTFLAG}} != 0) {
          $exitcode=1;
        }
      }
    }
  }

  if ($opt_RebootDevice) {
    if ($exitcode or length($opt_MACAddress)==0) {
      print "Reboot request skipped due to failed previous operation\n"
    } else {
      my $payload=pack("H*",$opt_MACAddress).pack("C",length($opt_Password)).$opt_Password;
      addp_broadcast(+ADDP_PACKET_REBOOT_REQUEST,$payload,$ViewLVL,1,1,0);
    }
  }

  if (length($opt_DataRead)) {
    my $fh;
    open($fh, '<', $opt_DataRead) or die();
    my $type;
    my $dir;
    my $addr;
    my $msg;
    my @snmplist=();
    while (<$fh>) {
      chomp();
      if (not $_ =~ m/^\s*\#/ ) {
        ($type,$dir,$addr,$msg)=split(/,/,$_);
        $msg =~ s/\s//g;
        $msg=pack("H*",$msg);
        printf("%s %s %s length %u\n",$type,$dir,$addr,length($msg));
        if ($type eq 'addp') {
          print "\n";
          addp_decode($ViewLVL,$dir,$addr,$msg); # probably destroys $_
        } elsif ($type eq 'snmp') {
          my $tmplvl=$opt_Debug?$ViewLVL:0;
          print "\n" if ($tmplvl);
          #print space_hex($msg,1),"\n";
          snmp_decode_recur(0,0,$msg,$tmplvl,{From=>$addr}); # probably destroys $_
          if ($dir eq "from") {
            $addr =~ s/:.+$//g;
            push(@snmplist,[inet_aton($addr),$msg]);
          }
        }
      }
    }
    close($fh);
    #print Dumper(\@snmplist),"\n";
    if (scalar @snmplist) {
      my %hsnmp=snmp_assemble(\@snmplist,$ViewLVL,{},1);
      print Dumper(\%hsnmp);
    }
  }

  if (length($opt_DecodeAddp)) {
    if (not addp_decode($ViewLVL,"from","commandline",pack("H*",$opt_DecodeAddp))) { # probably destroys $_
      print "Did you copy the whole ethernet frame by mistake? Try copying only the data portion of the UDP packet.\n";
      print "Don't copy 'User Datagram Protocol.' Copy the one below it called 'Distributed Interactive Simulation.'\n";
    }
  }

  if (length($opt_SignedBytes)) {
    $opt_SignedBytes =~ s/,/ /g;
    my @sbn=split(/\s+/,$opt_SignedBytes);
    my $hex='';
    foreach(@sbn) {
      $_=256+$_ if ($_ < 0);
      $hex .= pack("C",$_);
    }
    print "length=",length($hex)," ",unpack("H*",$hex),"\n";
  }

  #print "Exit=$exitcode\n";
  return $exitcode;
}

exit(main());
