#!/usr/bin/ruby

# experimental script for finding axiom sets suitable for proofs with SPASS
require 'open3'
require 'io/wait'

def send_cmd(cmd,stdin,stdout,wait=false,waitfor=nil)
#  puts "\e[01;36m#{cmd}\e[00m"
  stdin.puts cmd
  if wait then
    out = ""
    loop do
      sleep 0.03
      len = stdout.ready?
      if len
        out1 = stdout.sysread(len)
#        print out1
        out << out1
        if waitfor.nil? or out.include?(waitfor)
          return out
        end
      end
    end  
  else
    return ""
  end
end

def prove(axs,stdin,stdout)
  send_cmd("prover SPASS",stdin,stdout)
  send_cmd("set time-limit 10",stdin,stdout)
  send_cmd("set goals case_2a_02",stdin,stdout)
  send_cmd("set axioms #{axs.join(' ')}",stdin,stdout)
  out = send_cmd("prove",stdin,stdout,true,"Goal ")
  if out.include?(" proved") then 
    puts axs.inspect
    return :proved
  end
  if out.include?(" disproved") then 
    return :disproved
  end
  return :open
end

Open3.popen3('hets -I') do | stdin, stdout, stderr |
  File.read("init.hpf").each_line do |line|
    line.chomp!
    send_cmd(line,stdin,stdout,line=="prove","Goal ")
  end
  axs = {}
  send_cmd("show-all-axioms-current",stdin,stdout,true).each_line do |ax|
    ax.chomp!
    axs[ax] = if ["second_price_auction_winners_payment_def","case_2a_pre_02","maximum_is_component","ga_non_empty_sort_index","maximum_sufficient","gt_one_imp_gt_0","second_price_auction_winners_payment_def","arg_max_set_def","second_price_auction_def","ga_non_empty_sort_participant","ga_non_empty_sort_bids","deviation_def_index","deviation_vec_range","deviation_vec_def","deviation_range","remaining_maximum_invariant","i_sticks_with_valuation_def","case_2a_pre_02"].include?(ax) then 10000 else 9990 end
  end

  temperature = 1000
  loop do
    sorted_axs = axs.sort_by { |ax, val| -val+rand(100)*temperature/1000 }
    puts
    sorted_axs.each do |a|
      puts "#{a[1]}: #{a[0]}"
    end
    sorted_axs = sorted_axs.map{|a| a[0]}
    for i in (1..sorted_axs.length)
      axs_for_proof = sorted_axs[0..i-1]
      case prove(axs_for_proof,stdin,stdout) 
        when :proved
          puts axs_for_proof.inspect
          exit
        when :disproved
          if i>5 then
            axs[axs_for_proof[-1]] += i
          end
        when :open
          break
      end
    end
    temperature -= 1
  end

end

