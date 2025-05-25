--[[
 .____                  ________ ___.    _____                           __                
 |    |    __ _______   \_____  \\_ |___/ ____\_ __  ______ ____ _____ _/  |_  ___________ 
 |    |   |  |  \__  \   /   |   \| __ \   __\  |  \/  ___// ___\\__  \\   __\/  _ \_  __ \
 |    |___|  |  // __ \_/    |    \ \_\ \  | |  |  /\___ \\  \___ / __ \|  | (  <_> )  | \/
 |_______ \____/(____  /\_______  /___  /__| |____//____  >\___  >____  /__|  \____/|__|   
         \/          \/         \/    \/                \/     \/     \/                   
          \_Welcome to LuaObfuscator.com   (Alpha 0.10.9) ~  Much Love, Ferib 

]]--

local StrToNumber = tonumber;
local Byte = string.byte;
local Char = string.char;
local Sub = string.sub;
local Subg = string.gsub;
local Rep = string.rep;
local Concat = table.concat;
local Insert = table.insert;
local LDExp = math.ldexp;
local GetFEnv = getfenv or function()
	return _ENV;
end;
local Setmetatable = setmetatable;
local PCall = pcall;
local Select = select;
local Unpack = unpack or table.unpack;
local ToNumber = tonumber;
local function VMCall(ByteString, vmenv, ...)
	local DIP = 1;
	local repeatNext;
	ByteString = Subg(Sub(ByteString, 5), "..", function(byte)
		if (Byte(byte, 2) == 81) then
			repeatNext = StrToNumber(Sub(byte, 1, 1));
			return "";
		else
			local a = Char(StrToNumber(byte, 16));
			if repeatNext then
				local b = Rep(a, repeatNext);
				repeatNext = nil;
				return b;
			else
				return a;
			end
		end
	end);
	local function gBit(Bit, Start, End)
		if End then
			local Res = (Bit / (2 ^ (Start - 1))) % (2 ^ (((End - 1) - (Start - 1)) + 1));
			return Res - (Res % 1);
		else
			local Plc = 2 ^ (Start - 1);
			return (((Bit % (Plc + Plc)) >= Plc) and 1) or 0;
		end
	end
	local function gBits8()
		local a = Byte(ByteString, DIP, DIP);
		DIP = DIP + 1;
		return a;
	end
	local function gBits16()
		local a, b = Byte(ByteString, DIP, DIP + 2);
		DIP = DIP + 2;
		return (b * 256) + a;
	end
	local function gBits32()
		local a, b, c, d = Byte(ByteString, DIP, DIP + 3);
		DIP = DIP + 4;
		return (d * 16777216) + (c * 65536) + (b * 256) + a;
	end
	local function gFloat()
		local Left = gBits32();
		local Right = gBits32();
		local IsNormal = 1;
		local Mantissa = (gBit(Right, 1, 20) * (2 ^ 32)) + Left;
		local Exponent = gBit(Right, 21, 31);
		local Sign = ((gBit(Right, 32) == 1) and -1) or 1;
		if (Exponent == 0) then
			if (Mantissa == 0) then
				return Sign * 0;
			else
				Exponent = 1;
				IsNormal = 0;
			end
		elseif (Exponent == 2047) then
			return ((Mantissa == 0) and (Sign * (1 / 0))) or (Sign * NaN);
		end
		return LDExp(Sign, Exponent - 1023) * (IsNormal + (Mantissa / (2 ^ 52)));
	end
	local function gString(Len)
		local Str;
		if not Len then
			Len = gBits32();
			if (Len == 0) then
				return "";
			end
		end
		Str = Sub(ByteString, DIP, (DIP + Len) - 1);
		DIP = DIP + Len;
		local FStr = {};
		for Idx = 1, #Str do
			FStr[Idx] = Char(Byte(Sub(Str, Idx, Idx)));
		end
		return Concat(FStr);
	end
	local gInt = gBits32;
	local function _R(...)
		return {...}, Select("#", ...);
	end
	local function Deserialize()
		local Instrs = {};
		local Functions = {};
		local Lines = {};
		local Chunk = {Instrs,Functions,nil,Lines};
		local ConstCount = gBits32();
		local Consts = {};
		for Idx = 1, ConstCount do
			local Type = gBits8();
			local Cons;
			if (Type == 1) then
				Cons = gBits8() ~= 0;
			elseif (Type == 2) then
				Cons = gFloat();
			elseif (Type == 3) then
				Cons = gString();
			end
			Consts[Idx] = Cons;
		end
		Chunk[3] = gBits8();
		for Idx = 1, gBits32() do
			local Descriptor = gBits8();
			if (gBit(Descriptor, 1, 1) == 0) then
				local Type = gBit(Descriptor, 2, 3);
				local Mask = gBit(Descriptor, 4, 6);
				local Inst = {gBits16(),gBits16(),nil,nil};
				if (Type == 0) then
					Inst[3] = gBits16();
					Inst[4] = gBits16();
				elseif (Type == 1) then
					Inst[3] = gBits32();
				elseif (Type == 2) then
					Inst[3] = gBits32() - (2 ^ 16);
				elseif (Type == 3) then
					Inst[3] = gBits32() - (2 ^ 16);
					Inst[4] = gBits16();
				end
				if (gBit(Mask, 1, 1) == 1) then
					Inst[2] = Consts[Inst[2]];
				end
				if (gBit(Mask, 2, 2) == 1) then
					Inst[3] = Consts[Inst[3]];
				end
				if (gBit(Mask, 3, 3) == 1) then
					Inst[4] = Consts[Inst[4]];
				end
				Instrs[Idx] = Inst;
			end
		end
		for Idx = 1, gBits32() do
			Functions[Idx - 1] = Deserialize();
		end
		return Chunk;
	end
	local function Wrap(Chunk, Upvalues, Env)
		local Instr = Chunk[1];
		local Proto = Chunk[2];
		local Params = Chunk[3];
		return function(...)
			local Instr = Instr;
			local Proto = Proto;
			local Params = Params;
			local _R = _R;
			local VIP = 1;
			local Top = -1;
			local Vararg = {};
			local Args = {...};
			local PCount = Select("#", ...) - 1;
			local Lupvals = {};
			local Stk = {};
			for Idx = 0, PCount do
				if (Idx >= Params) then
					Vararg[Idx - Params] = Args[Idx + 1];
				else
					Stk[Idx] = Args[Idx + 1];
				end
			end
			local Varargsz = (PCount - Params) + 1;
			local Inst;
			local Enum;
			while true do
				Inst = Instr[VIP];
				Enum = Inst[1];
				if (Enum <= 48) then
					if (Enum <= 23) then
						if (Enum <= 11) then
							if (Enum <= 5) then
								if (Enum <= 2) then
									if (Enum <= 0) then
										local B;
										local A;
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									elseif (Enum > 1) then
										if not Stk[Inst[2]] then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									else
										Stk[Inst[2]] = Inst[3];
									end
								elseif (Enum <= 3) then
									local B;
									local A;
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
								elseif (Enum == 4) then
									local K;
									local B;
									local A;
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Stk[Inst[4]]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = #Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									B = Inst[3];
									K = Stk[B];
									for Idx = B + 1, Inst[4] do
										K = K .. Stk[Idx];
									end
									Stk[Inst[2]] = K;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
								else
									VIP = Inst[3];
								end
							elseif (Enum <= 8) then
								if (Enum <= 6) then
									local A;
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return;
									end
								elseif (Enum > 7) then
									local A;
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if (Stk[Inst[2]] < Stk[Inst[4]]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
									local A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								end
							elseif (Enum <= 9) then
								Stk[Inst[2]] = #Stk[Inst[3]];
							elseif (Enum == 10) then
								local B;
								local T;
								local A;
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								T = Stk[A];
								B = Inst[3];
								for Idx = 1, B do
									T[Idx] = Stk[A + Idx];
								end
							else
								local B;
								local T;
								local A;
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								T = Stk[A];
								B = Inst[3];
								for Idx = 1, B do
									T[Idx] = Stk[A + Idx];
								end
							end
						elseif (Enum <= 17) then
							if (Enum <= 14) then
								if (Enum <= 12) then
									Stk[Inst[2]][Inst[3]] = Inst[4];
								elseif (Enum == 13) then
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								else
									for Idx = Inst[2], Inst[3] do
										Stk[Idx] = nil;
									end
								end
							elseif (Enum <= 15) then
								local A;
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							elseif (Enum == 16) then
								local B;
								local A;
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
							else
								local A;
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = #Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]]();
							end
						elseif (Enum <= 20) then
							if (Enum <= 18) then
								do
									return Stk[Inst[2]];
								end
							elseif (Enum > 19) then
								local B;
								local T;
								local A;
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								T = Stk[A];
								B = Inst[3];
								for Idx = 1, B do
									T[Idx] = Stk[A + Idx];
								end
							else
								local A = Inst[2];
								local T = Stk[A];
								local B = Inst[3];
								for Idx = 1, B do
									T[Idx] = Stk[A + Idx];
								end
							end
						elseif (Enum <= 21) then
							local B;
							local A;
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
						elseif (Enum == 22) then
							local B;
							local A;
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
						else
							local B;
							local A;
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							do
								return;
							end
						end
					elseif (Enum <= 35) then
						if (Enum <= 29) then
							if (Enum <= 26) then
								if (Enum <= 24) then
									local B;
									local A;
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
								elseif (Enum > 25) then
									local B;
									local A;
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
								else
									local B;
									local A;
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								end
							elseif (Enum <= 27) then
								local B;
								local A;
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
							elseif (Enum > 28) then
								Stk[Inst[2]] = Stk[Inst[3]];
							else
								local B;
								local A;
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
							end
						elseif (Enum <= 32) then
							if (Enum <= 30) then
								local B;
								local A;
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							elseif (Enum == 31) then
								local A = Inst[2];
								local T = Stk[A];
								for Idx = A + 1, Inst[3] do
									Insert(T, Stk[Idx]);
								end
							else
								local B;
								local A;
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
							end
						elseif (Enum <= 33) then
							local A = Inst[2];
							local Step = Stk[A + 2];
							local Index = Stk[A] + Step;
							Stk[A] = Index;
							if (Step > 0) then
								if (Index <= Stk[A + 1]) then
									VIP = Inst[3];
									Stk[A + 3] = Index;
								end
							elseif (Index >= Stk[A + 1]) then
								VIP = Inst[3];
								Stk[A + 3] = Index;
							end
						elseif (Enum == 34) then
							local B;
							local A;
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = {};
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
						else
							local B;
							local A;
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
						end
					elseif (Enum <= 41) then
						if (Enum <= 38) then
							if (Enum <= 36) then
								if Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum > 37) then
								if (Stk[Inst[2]] < Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								local B;
								local A;
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
							end
						elseif (Enum <= 39) then
							local A = Inst[2];
							local Results = {Stk[A](Stk[A + 1])};
							local Edx = 0;
							for Idx = A, Inst[4] do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						elseif (Enum == 40) then
							local B;
							local A;
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = {};
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]]();
						else
							local A = Inst[2];
							do
								return Unpack(Stk, A, A + Inst[3]);
							end
						end
					elseif (Enum <= 44) then
						if (Enum <= 42) then
							local B;
							local A;
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
						elseif (Enum > 43) then
							local A;
							A = Inst[2];
							Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
						else
							local A = Inst[2];
							local B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Stk[Inst[4]]];
						end
					elseif (Enum <= 46) then
						if (Enum > 45) then
							local A = Inst[2];
							local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
							Top = (Limit + A) - 1;
							local Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						else
							local B;
							local T;
							local A;
							Stk[Inst[2]] = {};
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							T = Stk[A];
							B = Inst[3];
							for Idx = 1, B do
								T[Idx] = Stk[A + Idx];
							end
						end
					elseif (Enum > 47) then
						Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
					else
						local B;
						local A;
						A = Inst[2];
						Stk[A](Unpack(Stk, A + 1, Inst[3]));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						B = Stk[Inst[3]];
						Stk[A + 1] = B;
						Stk[A] = B[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						B = Stk[Inst[3]];
						Stk[A + 1] = B;
						Stk[A] = B[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A](Unpack(Stk, A + 1, Inst[3]));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						B = Stk[Inst[3]];
						Stk[A + 1] = B;
						Stk[A] = B[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
					end
				elseif (Enum <= 72) then
					if (Enum <= 60) then
						if (Enum <= 54) then
							if (Enum <= 51) then
								if (Enum <= 49) then
									local A = Inst[2];
									Stk[A](Stk[A + 1]);
								elseif (Enum > 50) then
									local B;
									local A;
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
								else
									local B = Inst[3];
									local K = Stk[B];
									for Idx = B + 1, Inst[4] do
										K = K .. Stk[Idx];
									end
									Stk[Inst[2]] = K;
								end
							elseif (Enum <= 52) then
								local B;
								local A;
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
							elseif (Enum == 53) then
								Upvalues[Inst[3]] = Stk[Inst[2]];
							else
								local B;
								local A;
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
							end
						elseif (Enum <= 57) then
							if (Enum <= 55) then
								local B;
								local A;
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
							elseif (Enum > 56) then
								if (Inst[2] < Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								local K;
								local B;
								local A;
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								B = Inst[3];
								K = Stk[B];
								for Idx = B + 1, Inst[4] do
									K = K .. Stk[Idx];
								end
								Stk[Inst[2]] = K;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
							end
						elseif (Enum <= 58) then
							local A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
						elseif (Enum > 59) then
							local B;
							local T;
							local A;
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							T = Stk[A];
							B = Inst[3];
							for Idx = 1, B do
								T[Idx] = Stk[A + Idx];
							end
						else
							local A;
							A = Inst[2];
							Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
						end
					elseif (Enum <= 66) then
						if (Enum <= 63) then
							if (Enum <= 61) then
								local A;
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Upvalues[Inst[3]] = Stk[Inst[2]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							elseif (Enum == 62) then
								local B;
								local A;
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
							else
								local B;
								local A;
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
							end
						elseif (Enum <= 64) then
							Stk[Inst[2]] = Upvalues[Inst[3]];
						elseif (Enum > 65) then
							local B;
							local A;
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Stk[Inst[4]]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
						else
							local B;
							local A;
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
						end
					elseif (Enum <= 69) then
						if (Enum <= 67) then
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						elseif (Enum > 68) then
							local A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
						else
							local B;
							local A;
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
						end
					elseif (Enum <= 70) then
						Stk[Inst[2]] = Env[Inst[3]];
					elseif (Enum == 71) then
						local NewProto = Proto[Inst[3]];
						local NewUvals;
						local Indexes = {};
						NewUvals = Setmetatable({}, {__index=function(_, Key)
							local Val = Indexes[Key];
							return Val[1][Val[2]];
						end,__newindex=function(_, Key, Value)
							local Val = Indexes[Key];
							Val[1][Val[2]] = Value;
						end});
						for Idx = 1, Inst[4] do
							VIP = VIP + 1;
							local Mvm = Instr[VIP];
							if (Mvm[1] == 29) then
								Indexes[Idx - 1] = {Stk,Mvm[3]};
							else
								Indexes[Idx - 1] = {Upvalues,Mvm[3]};
							end
							Lupvals[#Lupvals + 1] = Indexes;
						end
						Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
					else
						local B;
						local A;
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						B = Stk[Inst[3]];
						Stk[A + 1] = B;
						Stk[A] = B[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A](Unpack(Stk, A + 1, Inst[3]));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						do
							return;
						end
					end
				elseif (Enum <= 84) then
					if (Enum <= 78) then
						if (Enum <= 75) then
							if (Enum <= 73) then
								Stk[Inst[2]] = {};
							elseif (Enum == 74) then
								local B;
								local A;
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
							else
								local B;
								local T;
								local A;
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								T = Stk[A];
								B = Inst[3];
								for Idx = 1, B do
									T[Idx] = Stk[A + Idx];
								end
							end
						elseif (Enum <= 76) then
							local B;
							local A;
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = {};
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum > 77) then
							local B;
							local A;
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = {};
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]]();
						else
							local Step;
							local Index;
							local B;
							local A;
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Index = Stk[A];
							Step = Stk[A + 2];
							if (Step > 0) then
								if (Index > Stk[A + 1]) then
									VIP = Inst[3];
								else
									Stk[A + 3] = Index;
								end
							elseif (Index < Stk[A + 1]) then
								VIP = Inst[3];
							else
								Stk[A + 3] = Index;
							end
						end
					elseif (Enum <= 81) then
						if (Enum <= 79) then
							local B;
							local A;
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
						elseif (Enum > 80) then
							local B;
							local A;
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						else
							local A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
						end
					elseif (Enum <= 82) then
						local T;
						local K;
						local B;
						local A;
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A] = Stk[A](Stk[A + 1]);
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = {};
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = {};
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = {};
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Inst[4];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Inst[4];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Inst[4];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = {};
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						B = Inst[3];
						K = Stk[B];
						for Idx = B + 1, Inst[4] do
							K = K .. Stk[Idx];
						end
						Stk[Inst[2]] = K;
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = {};
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = {};
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Inst[4];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						B = Inst[3];
						K = Stk[B];
						for Idx = B + 1, Inst[4] do
							K = K .. Stk[Idx];
						end
						Stk[Inst[2]] = K;
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Inst[4];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = {};
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Inst[4];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						B = Stk[Inst[3]];
						Stk[A + 1] = B;
						Stk[A] = B[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A] = Stk[A](Stk[A + 1]);
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = #Stk[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						B = Inst[3];
						K = Stk[B];
						for Idx = B + 1, Inst[4] do
							K = K .. Stk[Idx];
						end
						Stk[Inst[2]] = K;
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Inst[4];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = {};
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Inst[4];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						B = Inst[3];
						K = Stk[B];
						for Idx = B + 1, Inst[4] do
							K = K .. Stk[Idx];
						end
						Stk[Inst[2]] = K;
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Inst[4];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						T = Stk[A];
						B = Inst[3];
						for Idx = 1, B do
							T[Idx] = Stk[A + Idx];
						end
					elseif (Enum == 83) then
						local A = Inst[2];
						local B = Stk[Inst[3]];
						Stk[A + 1] = B;
						Stk[A] = B[Inst[4]];
					else
						local A;
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = {};
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Inst[4];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = {};
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Inst[4];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A](Stk[A + 1]);
						VIP = VIP + 1;
						Inst = Instr[VIP];
						do
							return;
						end
					end
				elseif (Enum <= 90) then
					if (Enum <= 87) then
						if (Enum <= 85) then
							Stk[Inst[2]] = Wrap(Proto[Inst[3]], nil, Env);
						elseif (Enum > 86) then
							local A = Inst[2];
							Stk[A] = Stk[A]();
						else
							local B;
							local T;
							local A;
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							T = Stk[A];
							B = Inst[3];
							for Idx = 1, B do
								T[Idx] = Stk[A + Idx];
							end
						end
					elseif (Enum <= 88) then
						local B;
						local A;
						A = Inst[2];
						Stk[A](Unpack(Stk, A + 1, Inst[3]));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						B = Stk[Inst[3]];
						Stk[A + 1] = B;
						Stk[A] = B[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
					elseif (Enum == 89) then
						Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
					else
						local Edx;
						local Results, Limit;
						local B;
						local A;
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						B = Stk[Inst[3]];
						Stk[A + 1] = B;
						Stk[A] = B[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
						Top = (Limit + A) - 1;
						Edx = 0;
						for Idx = A, Top do
							Edx = Edx + 1;
							Stk[Idx] = Results[Edx];
						end
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A] = Stk[A]();
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Upvalues[Inst[3]] = Stk[Inst[2]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						do
							return;
						end
					end
				elseif (Enum <= 93) then
					if (Enum <= 91) then
						do
							return;
						end
					elseif (Enum == 92) then
						Stk[Inst[2]]();
					else
						local A = Inst[2];
						local Index = Stk[A];
						local Step = Stk[A + 2];
						if (Step > 0) then
							if (Index > Stk[A + 1]) then
								VIP = Inst[3];
							else
								Stk[A + 3] = Index;
							end
						elseif (Index < Stk[A + 1]) then
							VIP = Inst[3];
						else
							Stk[A + 3] = Index;
						end
					end
				elseif (Enum <= 95) then
					if (Enum > 94) then
						local B;
						local A;
						A = Inst[2];
						Stk[A](Unpack(Stk, A + 1, Inst[3]));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						B = Stk[Inst[3]];
						Stk[A + 1] = B;
						Stk[A] = B[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						B = Stk[Inst[3]];
						Stk[A + 1] = B;
						Stk[A] = B[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A](Unpack(Stk, A + 1, Inst[3]));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						B = Stk[Inst[3]];
						Stk[A + 1] = B;
						Stk[A] = B[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
					else
						local B;
						local A;
						A = Inst[2];
						Stk[A](Unpack(Stk, A + 1, Inst[3]));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						B = Stk[Inst[3]];
						Stk[A + 1] = B;
						Stk[A] = B[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						B = Stk[Inst[3]];
						Stk[A + 1] = B;
						Stk[A] = B[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						B = Stk[Inst[3]];
						Stk[A + 1] = B;
						Stk[A] = B[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A](Unpack(Stk, A + 1, Inst[3]));
					end
				elseif (Enum > 96) then
					local K;
					local B;
					Stk[Inst[2]] = Inst[3];
					VIP = VIP + 1;
					Inst = Instr[VIP];
					Stk[Inst[2]] = Inst[3];
					VIP = VIP + 1;
					Inst = Instr[VIP];
					Stk[Inst[2]] = Inst[3];
					VIP = VIP + 1;
					Inst = Instr[VIP];
					Stk[Inst[2]] = Stk[Inst[3]];
					VIP = VIP + 1;
					Inst = Instr[VIP];
					Stk[Inst[2]] = Stk[Inst[3]];
					VIP = VIP + 1;
					Inst = Instr[VIP];
					Stk[Inst[2]] = Stk[Inst[3]];
					VIP = VIP + 1;
					Inst = Instr[VIP];
					B = Inst[3];
					K = Stk[B];
					for Idx = B + 1, Inst[4] do
						K = K .. Stk[Idx];
					end
					Stk[Inst[2]] = K;
					VIP = VIP + 1;
					Inst = Instr[VIP];
					do
						return Stk[Inst[2]];
					end
					VIP = VIP + 1;
					Inst = Instr[VIP];
					do
						return;
					end
				else
					local B;
					local A;
					A = Inst[2];
					Stk[A](Unpack(Stk, A + 1, Inst[3]));
					VIP = VIP + 1;
					Inst = Instr[VIP];
					A = Inst[2];
					B = Stk[Inst[3]];
					Stk[A + 1] = B;
					Stk[A] = B[Inst[4]];
					VIP = VIP + 1;
					Inst = Instr[VIP];
					Stk[Inst[2]] = Inst[3];
					VIP = VIP + 1;
					Inst = Instr[VIP];
					Stk[Inst[2]] = Inst[3];
					VIP = VIP + 1;
					Inst = Instr[VIP];
					Stk[Inst[2]] = Inst[3];
					VIP = VIP + 1;
					Inst = Instr[VIP];
					Stk[Inst[2]] = Inst[3];
				end
				VIP = VIP + 1;
			end
		end;
	end
	return Wrap(Deserialize(), {}, vmenv)(...);
end
return VMCall("LOL!34012Q0003043Q0067616D65030A3Q0047657453657276696365030F3Q0054656C65706F72745365727669636503073Q00506C6179657273030B3Q00482Q747053657276696365030B3Q004C6F63616C506C6179657202808F628A22E9D442028Q00025Q00C0724003053Q007063612Q6C030A3Q005374617274657247756903073Q00536574436F726503103Q0053656E644E6F74696669636174696F6E03053Q005469746C6503143Q00E29AA0EFB88F204C69627261727920452Q726F7203043Q005465787403313Q004661696C656420746F206C6F6164204B61766F205549206C6962726172792C207573696E672066612Q6C6261636B3Q2E03083Q004475726174696F6E026Q00144003103Q00E29AA0EFB88F2047554920452Q726F72032F3Q004661696C656420746F20637265617465206D61696E2077696E646F772C207573696E672066612Q6C6261636B3Q2E026Q00084003063Q004E6577546162030D3Q00F09F8EAD20526F6C65706C6179030A3Q004E657753656374696F6E03183Q00E29AA1204175746F20526F6C65706C61792053797374656D03083Q004E65774C6162656C03193Q00F09F8C9F20416476616E63656420525020466561747572657303093Q004E6577546F2Q676C6503123Q004175746F204A6F622053656C656374696F6E03203Q004175746F6D61746963612Q6C792073656C65637420616E6420646F206A6F627303153Q004175746F20526F6C65706C617920416374696F6E7303263Q00506572666F726D20726F6C65706C617920616374696F6E73206175746F6D61746963612Q6C7903133Q004175746F204368617420526573706F6E73657303263Q00526573706F6E6420746F206F7468657220706C6179657273206175746F6D61746963612Q6C79030B3Q004175746F20456D6F746573031A3Q0055736520656D6F74657320647572696E6720726F6C65706C617903093Q004E6577536C69646572030F3Q00525020416374696F6E2044656C6179031C3Q005365742064656C617920626574772Q656E20525020616374696F6E73026Q00F03F030F3Q00F09F9194204A6F622053797374656D03203Q00F09F94A72050726F66652Q73696F6E616C20526F6C65706C617920542Q6F6C73030B3Q004E657744726F70646F776E030A3Q0053656C656374204A6F6203163Q0043682Q6F736520796F75722070726F66652Q73696F6E030E3Q00506F6C696365204F2Q666963657203063Q00446F63746F72030B3Q00466972656669676874657203073Q005465616368657203043Q004368656603053Q0050696C6F7403073Q004361736869657203083Q004D656368616E696303093Q004E657742752Q746F6E030E3Q0047657420506F6C696365204A6F6203173Q004265636F6D65206120706F6C696365206F2Q6669636572030E3Q0047657420446F63746F72204A6F6203143Q00576F726B2061742074686520686F73706974616C030F3Q004765742054656163686572204A6F6203133Q00546561636820617420746865207363682Q6F6C030B3Q00F09F8FA020486F7573657303163Q00F09F8FA1204175746F20486F7573652053797374656D031A3Q00F09F8C9F20536D61727420486F6D65204D616E6167656D656E7403143Q004175746F20486F7573652053656C656374696F6E031C3Q004175746F6D61746963612Q6C7920676574206265737420686F75736503153Q004175746F20486F757365204465636F726174696F6E031C3Q004465636F7261746520686F757365206175746F6D61746963612Q6C7903183Q004175746F204675726E697475726520506C6163656D656E7403193Q00506C616365206675726E6974757265206F7074696D612Q6C7903103Q00486F7573652050726F74656374696F6E031B3Q0050726F7465637420686F7573652066726F6D20677269656665727303183Q00F09F8F98EFB88F20486F757365204D616E6167656D656E74031D3Q00F09F94A720486F6D6520437573746F6D697A6174696F6E20542Q6F6C73030A3Q00486F757365205479706503123Q0043682Q6F736520686F757365207374796C65030C3Q004D6F6465726E20486F757365030D3Q00436C612Q73696320486F75736503073Q004D616E73696F6E03093Q0041706172746D656E74030B3Q00426561636820486F75736503053Q00436162696E03093Q0050656E74686F757365030B3Q00476574204D616E73696F6E03153Q00476574207468652062692Q6765737420686F757365030F3Q0047657420426561636820486F75736503173Q0047657420776174657266726F6E742070726F706572747903163Q004465636F72617465204175746F6D61746963612Q6C7903163Q004175746F2D6675726E69736820796F757220686F6D65030D3Q00F09F9A972056656869636C657303173Q00E29AA1204175746F2056656869636C652053797374656D03193Q00F09F9A9720536D617274205472616E73706F72746174696F6E03123Q004175746F20537061776E2056656869636C65031C3Q004175746F6D61746963612Q6C7920737061776E2076656869636C6573030A3Q004175746F20447269766503153Q0041492064726976696E6720612Q73697374616E636503133Q0056656869636C652053702Q656420422Q6F737403163Q00496E6372656173652076656869636C652073702Q656403113Q004E6F2056656869636C652044616D61676503173Q0050726576656E742076656869636C652063726173686573030D3Q0056656869636C652053702Q6564031C3Q005365742076656869636C652073702Q6564206D756C7469706C69657203173Q00F09F9A992056656869636C6520436F2Q6C656374696F6E03193Q00F09F94A7205472616E73706F72746174696F6E20542Q6F6C73030C3Q0056656869636C65205479706503103Q0043682Q6F736520796F75722072696465030A3Q0053706F72747320436172030A3Q004D6F746F726379636C6503053Q00547275636B2Q033Q00427573030A3Q0048656C69636F7074657203043Q00426F617403073Q0042696379636C65030A3Q00536B617465626F61726403103Q00537061776E2053706F72747320436172030F3Q0047657420666173746573742063617203103Q00537061776E2048656C69636F7074657203123Q004765742061657269616C2076656869636C6503123Q00537061776E20412Q6C2056656869636C657303113Q004765742065766572792076656869636C65030B3Q00F09F91A520536F6369616C03173Q00F09FA49D204175746F20536F6369616C2053797374656D031D3Q00F09F8C9F20536F6369616C20496E746572616374696F6E20542Q6F6C7303143Q004175746F20467269656E6420526571756573747303223Q0053656E6420667269656E64207265717565737473206175746F6D61746963612Q6C7903093Q004175746F204368617403173Q00436861742077697468206F7468657220706C617965727303133Q004175746F20466F2Q6C6F7720506C6179657273031A3Q00466F2Q6C6F7720696E746572657374696E6720706C6179657273030A3Q005061727479204D6F646503163Q004A6F696E206F7220637265617465207061727469657303113Q00F09F8EAC205250205363656E6172696F73031B3Q00F09F8EAD20526F6C65706C61792053746F72792043726561746F72030B3Q005250205363656E6172696F03183Q0043682Q6F736520726F6C65706C6179207363656E6172696F030B3Q0046616D696C79204C696665030A3Q005363682Q6F6C20446179030E3Q00486F73706974616C204472616D61030C3Q00506F6C69636520436861736503123Q0052657374617572616E742053657276696365030D3Q0053686F2Q70696E672054726970030B3Q004265616368205061727479030F3Q0053746172742046616D696C7920525003153Q00426567696E2066616D696C7920726F6C65706C6179030F3Q005374617274205363682Q6F6C20525003153Q00426567696E207363682Q6F6C207363656E6172696F030A3Q00486F737420506172747903163Q004F7267616E697A652061207061727479206576656E7403133Q00F09F97BAEFB88F204578706C6F726174696F6E03153Q00F09F948D204175746F204578706C6F726174696F6E03193Q00F09F8C9F204D617020446973636F766572792053797374656D03103Q004175746F204578706C6F7265204D617003203Q004175746F6D61746963612Q6C79206578706C6F72652042722Q6F6B686176656E03163Q00536563726574204C6F636174696F6E2046696E64657203113Q0046696E642068692Q64656E20617265617303123Q004175746F20436F2Q6C656374204974656D7303183Q00436F2Q6C656374206974656D732061726F756E64206D617003113Q004C6F636174696F6E204E6F74696669657203223Q00476574206E6F746966696564206F6620696E746572657374696E6720706C6163657303163Q00F09F938D204C6F636174696F6E2054656C65706F727403193Q00E29AA120496E7374616E742054726176656C2053797374656D03133Q004C6F636174696F6E2054656C65706F7274657203153Q0054656C65706F727420746F206C6F636174696F6E73030B3Q00546F776E2043656E74657203063Q005363682Q6F6C03083Q00486F73706974616C030E3Q00506F6C6963652053746174696F6E03053Q00426561636803073Q00416972706F727403043Q004D612Q6C03043Q005061726B03123Q0054656C65706F727420746F205363682Q6F6C03163Q00476F20746F20656475636174696F6E616C206172656103143Q0054656C65706F727420746F20486F73706974616C03143Q005669736974206D65646963616C2063656E74657203113Q0054656C65706F727420746F20426561636803103Q00476F20746F20776174657266726F6E7403113Q00E29CA820437573746F6D697A6174696F6E03193Q00F09F91A42041766174617220437573746F6D697A6174696F6E031A3Q00F09F8C9F2043686172616374657220456E68616E63656D656E7403123Q004175746F204F7574666974204368616E6765031C3Q004368616E6765206F757466697473206175746F6D61746963612Q6C79030D3Q005374796C65204D61746368657203183Q004D61746368207374796C65207769746820667269656E647303133Q00476574205072656D69756D20436C6F7468657303183Q00412Q63652Q73206578636C7573697665206F757466697473030D3Q0052616E646F6D204F757466697403153Q0047656E65726174652072616E646F6D207374796C65030F3Q00F09F90BE205065742053797374656D031B3Q00F09F9095205669727475616C20506574204D616E6167656D656E74030D3Q004175746F205065742043617265031F3Q0054616B652063617265206F662070657473206175746F6D61746963612Q6C7903083Q00506574205479706503153Q0043682Q6F736520796F757220636F6D70616E696F6E2Q033Q00446F672Q033Q0043617403063Q0052612Q62697403043Q004269726403043Q004669736803073Q0048616D7374657203063Q00547572746C6503053Q00486F727365030C3Q0047657420412Q6C2050657473030F3Q0041646F707420657665727920706574030E3Q00F09F9181EFB88F2056697375616C030F3Q00F09F8C9F204553502053797374656D031D3Q00F09F918020456E68616E63656420566973696F6E204665617475726573030A3Q00506C6179657220455350031D3Q00532Q6520612Q6C20706C6179657273207468726F7567682077612Q6C73030B3Q0056656869636C652045535003113Q0053686F7720612Q6C2076656869636C657303093Q00486F7573652045535003143Q00486967686C6967687420612Q6C20686F7573657303083Q004974656D2045535003163Q0053686F7720636F2Q6C65637469626C65206974656D73030F3Q0053656372657420417265612045535003173Q0052657665616C2068692Q64656E206C6F636174696F6E73030E3Q004E6577436F6C6F725069636B657203093Q0045535020436F6C6F7203173Q004368616E67652045535020636F6C6F7220736368656D6503063Q00436F6C6F723303073Q0066726F6D524742025Q00E06F4003123Q00E29CA82056697375616C20452Q6665637473031F3Q00F09F8C9F20456E7669726F6E6D656E74616C20456E68616E63656D656E7473030A3Q0046752Q6C627269676874030F3Q0052656D6F7665206461726B6E652Q73030C3Q005261696E626F77204D6F646503143Q00436F6C6F7266756C20656E7669726F6E6D656E74030D3Q004669656C64206F66205669657703113Q0041646A7573742063616D65726120464F56026Q005E40025Q0080514003093Q00F09F94A7204D69736303103Q00E29A99EFB88F205574696C697469657303203Q00F09F9BA0EFB88F205175616C697479206F66204C69666520466561747572657303083Q00416E74692041464B03163Q0050726576656E742067652Q74696E67206B69636B6564030B3Q004175746F2052656A6F696E03143Q0052656A6F696E206F6E20646973636F2Q6E656374030B3Q0053702Q656420422Q6F7374030B3Q004D6F766520666173746572030A3Q004A756D7020422Q6F7374030B3Q004A756D7020686967686572030A3Q0057616C6B2053702Q656403153Q0041646A757374206D6F76656D656E742073702Q6564026Q005940026Q003040030A3Q004E65774B657962696E64030A3Q00546F2Q676C652047554903133Q0053686F772F4869646520696E7465726661636503043Q00456E756D03073Q004B6579436F6465030C3Q005269676874436F6E74726F6C03123Q00F09F8EAE2047616D6520466561747572657303163Q00F09F8C9F20456E68616E6365642047616D65706C617903133Q0046722Q652047616D6570612Q73204974656D7303143Q00412Q63652Q73207072656D69756D206974656D73030F3Q00556E6C696D697465642050726F7073031B3Q00506C61636520756E6C696D69746564206465636F726174696F6E7303133Q00556E6C6F636B20412Q6C20466561747572657303163Q004765742065766572792067616D652066656174757265030E3Q0041646D696E20436F2Q6D616E647303153Q00412Q63652Q732061646D696E20636F6E74726F6C73030F3Q00E29A99EFB88F2053652Q74696E677303123Q00F09F92BE20436F6E66696775726174696F6E03193Q00F09F938120536176652026204C6F61642053652Q74696E677303133Q00536176652043752Q72656E7420436F6E66696703113Q005361766520612Q6C2073652Q74696E677303113Q004C6F616420536176656420436F6E66696703163Q004C6F61642070726576696F75732073652Q74696E677303103Q00526573657420746F2044656661756C7403103Q0052657365742065766572797468696E67030A3Q004E657754657874426F78030B3Q00436F6E666967204E616D6503183Q00456E74657220636F6E66696775726174696F6E206E616D65030E3Q00F09F938A20416E616C797469637303153Q00F09F93882053652Q73696F6E20547261636B696E6703143Q0053656E642043752Q72656E742053652Q73696F6E03163Q004C6F672073652Q73696F6E20746F20776562682Q6F6B030E3Q004175746F20416E616C797469637303113Q004175746F206C6F672073652Q73696F6E73030F3Q0043752Q72656E74204A6F6249443A2003053Q004A6F62496403133Q00506C617965727320696E207365727665723A20030A3Q00476574506C6179657273030C3Q00E284B9EFB88F2041626F757403243Q00F09F8FA12042722Q6F6B686176656E20525020416476616E636564204875622076312E3003213Q00F09F8EAD20556C74696D61746520526F6C65706C617920457870657269656E6365030D3Q00436865636B205570646174657303113Q00436865636B20666F722075706461746573030C3Q004A6F696E20446973636F7264030E3Q004A6F696E20636F2Q6D756E697479030B3Q00476574205072656D69756D03173Q00556E6C6F636B207072656D69756D206665617475726573030B3Q00F09F8EA8205468656D6573031C3Q00F09F8C8820496E7465726661636520437573746F6D697A6174696F6E03083Q005549205468656D65030C3Q0043682Q6F7365207468656D65030A3Q004C696768745468656D6503093Q004461726B5468656D6503053Q004F6365616E030A3Q00426C2Q6F645468656D6503083Q0053656E74696E656C03073Q0053796E6170736503163Q00F09F8FA12042722Q6F6B686176656E20525020487562034D3Q00416476616E63656420726F6C65706C6179206665617475726573206C6F616465642120436C69636B20616E79206F7074696F6E20746F20612Q63652Q73207072656D69756D207365727665722E026Q0020400024032Q0012103Q00013Q00206Q000200122Q000200038Q0002000200122Q000100013Q00202Q00010001000200122Q000300046Q00010003000200122Q000200013Q00202Q000200020002001201000400054Q000700020004000200200D000300010006001201000400073Q00025500056Q001D000600054Q0057000600010002001201000700083Q001201000800093Q00064700090001000100062Q001D3Q00074Q001D3Q00084Q001D3Q00034Q001D3Q00014Q001D3Q00024Q001D3Q00063Q000647000A0002000100032Q001D8Q001D3Q00044Q001D3Q00033Q000647000B0003000100012Q001D3Q000A4Q000E000C000C3Q001246000D000A3Q000647000E0004000100012Q001D3Q000C4Q0027000D0002000E000602000D0033000100010004053Q00330001001246000F00013Q00204E000F000F000B00202Q000F000F000C00122Q0011000D6Q00123Q000300302Q0012000E000F00302Q00120010001100302Q0012001200134Q000F001200014Q000F000B6Q000F000100012Q005B3Q00014Q001D000F00094Q005C000F000100012Q000E000F000F3Q0012460010000A3Q00064700110005000100022Q001D3Q000F4Q001D3Q000C4Q0031001000020001000602000F0049000100010004053Q00490001001246001000013Q00204E00100010000B00202Q00100010000C00122Q0012000D6Q00133Q000300302Q0013000E001400302Q00130010001500302Q0013001200164Q0010001300014Q0010000B6Q0010000100012Q005B3Q00013Q0020530010000F0017001241001200186Q00100012000200202Q00110010001900122Q0013001A6Q00110013000200202Q00120011001B00122Q0014001C6Q00120014000100202Q00120011001D00122Q0014001E3Q0012010015001F3Q00064700160006000100012Q001D3Q000A4Q004500120016000100205300120011001D001201001400203Q001201001500213Q00064700160007000100012Q001D3Q000A4Q004500120016000100205300120011001D001201001400223Q001201001500233Q00064700160008000100012Q001D3Q000A4Q004500120016000100205300120011001D001201001400243Q001201001500253Q00064700160009000100012Q001D3Q000A4Q001B00120016000100202Q00120011002600122Q001400273Q00122Q001500283Q00122Q001600133Q00122Q001700293Q0006470018000A000100012Q001D3Q000A4Q002300120018000100202Q00120010001900122Q0014002A6Q00120014000200202Q00130012001B00122Q0015002B6Q00130015000100202Q00130012002C00122Q0015002D3Q00122Q0016002E4Q0049001700083Q00120B0018002F3Q00122Q001900303Q00122Q001A00313Q00122Q001B00323Q00122Q001C00333Q00122Q001D00343Q00122Q001E00353Q00122Q001F00366Q0017000800010006470018000B000100012Q001D3Q000A4Q0045001300180001002053001300120037001201001500383Q001201001600393Q0006470017000C000100012Q001D3Q000A4Q00450013001700010020530013001200370012010015003A3Q0012010016003B3Q0006470017000D000100012Q001D3Q000A4Q00450013001700010020530013001200370012010015003C3Q0012010016003D3Q0006470017000E000100012Q001D3Q000A4Q001600130017000100202Q0013000F001700122Q0015003E6Q00130015000200202Q00140013001900122Q0016003F6Q00140016000200202Q00150014001B00122Q001700406Q00150017000100205300150014001D001201001700413Q001201001800423Q0006470019000F000100012Q001D3Q000A4Q004500150019000100205300150014001D001201001700433Q001201001800443Q00064700190010000100012Q001D3Q000A4Q004500150019000100205300150014001D001201001700453Q001201001800463Q00064700190011000100012Q001D3Q000A4Q004500150019000100205300150014001D001201001700473Q001201001800483Q00064700190012000100012Q001D3Q000A4Q002300150019000100202Q00150013001900122Q001700496Q00150017000200202Q00160015001B00122Q0018004A6Q00160018000100202Q00160015002C00122Q0018004B3Q00122Q0019004C4Q0049001A00073Q00123C001B004D3Q00122Q001C004E3Q00122Q001D004F3Q00122Q001E00503Q00122Q001F00513Q00122Q002000523Q00122Q002100536Q001A00070001000647001B0013000100012Q001D3Q000A4Q00450016001B0001002053001600150037001201001800543Q001201001900553Q000647001A0014000100012Q001D3Q000A4Q00450016001A0001002053001600150037001201001800563Q001201001900573Q000647001A0015000100012Q001D3Q000A4Q00450016001A0001002053001600150037001201001800583Q001201001900593Q000647001A0016000100012Q001D3Q000A4Q00160016001A000100202Q0016000F001700122Q0018005A6Q00160018000200202Q00170016001900122Q0019005B6Q00170019000200202Q00180017001B00122Q001A005C6Q0018001A000100205300180017001D001201001A005D3Q001201001B005E3Q000647001C0017000100012Q001D3Q000A4Q00450018001C000100205300180017001D001201001A005F3Q001201001B00603Q000647001C0018000100012Q001D3Q000A4Q00450018001C000100205300180017001D001201001A00613Q001201001B00623Q000647001C0019000100012Q001D3Q000A4Q00450018001C000100205300180017001D001201001A00633Q001201001B00643Q000647001C001A000100012Q001D3Q000A4Q001B0018001C000100202Q00180017002600122Q001A00653Q00122Q001B00663Q00122Q001C00133Q00122Q001D00293Q000647001E001B000100012Q001D3Q000A4Q00230018001E000100202Q00180016001900122Q001A00676Q0018001A000200202Q00190018001B00122Q001B00686Q0019001B000100202Q00190018002C00122Q001B00693Q00122Q001C006A4Q0049001D00083Q00120B001E006B3Q00122Q001F006C3Q00122Q0020006D3Q00122Q0021006E3Q00122Q0022006F3Q00122Q002300703Q00122Q002400713Q00122Q002500726Q001D00080001000647001E001C000100012Q001D3Q000A4Q00450019001E0001002053001900180037001201001B00733Q001201001C00743Q000647001D001D000100012Q001D3Q000A4Q00450019001D0001002053001900180037001201001B00753Q001201001C00763Q000647001D001E000100012Q001D3Q000A4Q00450019001D0001002053001900180037001201001B00773Q001201001C00783Q000647001D001F000100012Q001D3Q000A4Q00160019001D000100202Q0019000F001700122Q001B00796Q0019001B000200202Q001A0019001900122Q001C007A6Q001A001C000200202Q001B001A001B00122Q001D007B6Q001B001D0001002053001B001A001D001201001D007C3Q001201001E007D3Q000647001F0020000100012Q001D3Q000A4Q0045001B001F0001002053001B001A001D001201001D007E3Q001201001E007F3Q000647001F0021000100012Q001D3Q000A4Q0045001B001F0001002053001B001A001D001201001D00803Q001201001E00813Q000647001F0022000100012Q001D3Q000A4Q0045001B001F0001002053001B001A001D001201001D00823Q001201001E00833Q000647001F0023000100012Q001D3Q000A4Q0023001B001F000100202Q001B0019001900122Q001D00846Q001B001D000200202Q001C001B001B00122Q001E00856Q001C001E000100202Q001C001B002C00122Q001E00863Q00122Q001F00874Q0049002000073Q00123C002100883Q00122Q002200893Q00122Q0023008A3Q00122Q0024008B3Q00122Q0025008C3Q00122Q0026008D3Q00122Q0027008E6Q00200007000100064700210024000100012Q001D3Q000A4Q0045001C00210001002053001C001B0037001201001E008F3Q001201001F00903Q00064700200025000100012Q001D3Q000A4Q0045001C00200001002053001C001B0037001201001E00913Q001201001F00923Q00064700200026000100012Q001D3Q000A4Q0045001C00200001002053001C001B0037001201001E00933Q001201001F00943Q00064700200027000100012Q001D3Q000A4Q0016001C0020000100202Q001C000F001700122Q001E00956Q001C001E000200202Q001D001C001900122Q001F00966Q001D001F000200202Q001E001D001B00122Q002000976Q001E00200001002053001E001D001D001201002000983Q001201002100993Q00064700220028000100012Q001D3Q000A4Q0045001E00220001002053001E001D001D0012010020009A3Q0012010021009B3Q00064700220029000100012Q001D3Q000A4Q0045001E00220001002053001E001D001D0012010020009C3Q0012010021009D3Q0006470022002A000100012Q001D3Q000A4Q0045001E00220001002053001E001D001D0012010020009E3Q0012010021009F3Q0006470022002B000100012Q001D3Q000A4Q0023001E0022000100202Q001E001C001900122Q002000A06Q001E0020000200202Q001F001E001B00122Q002100A16Q001F0021000100202Q001F001E002C00122Q002100A23Q00122Q002200A34Q0049002300083Q00120B002400A43Q00122Q002500A53Q00122Q002600A63Q00122Q002700A73Q00122Q002800A83Q00122Q002900A93Q00122Q002A00AA3Q00122Q002B00AB6Q0023000800010006470024002C000100012Q001D3Q000A4Q0045001F00240001002053001F001E0037001201002100AC3Q001201002200AD3Q0006470023002D000100012Q001D3Q000A4Q0045001F00230001002053001F001E0037001201002100AE3Q001201002200AF3Q0006470023002E000100012Q001D3Q000A4Q0045001F00230001002053001F001E0037001201002100B03Q001201002200B13Q0006470023002F000100012Q001D3Q000A4Q0016001F0023000100202Q001F000F001700122Q002100B26Q001F0021000200202Q0020001F001900122Q002200B36Q00200022000200202Q00210020001B00122Q002300B46Q00210023000100205300210020001D001201002300B53Q001201002400B63Q00064700250030000100012Q001D3Q000A4Q004500210025000100205300210020001D001201002300B73Q001201002400B83Q00064700250031000100012Q001D3Q000A4Q0045002100250001002053002100200037001201002300B93Q001201002400BA3Q00064700250032000100012Q001D3Q000A4Q0045002100250001002053002100200037001201002300BB3Q001201002400BC3Q00064700250033000100012Q001D3Q000A4Q002300210025000100202Q0021001F001900122Q002300BD6Q00210023000200202Q00220021001B00122Q002400BE6Q00220024000100202Q00220021001D00122Q002400BF3Q00122Q002500C03Q00064700260034000100012Q001D3Q000A4Q000300220026000100202Q00220021002C00122Q002400C13Q00122Q002500C26Q002600083Q00122Q002700C33Q00122Q002800C43Q00122Q002900C53Q00122Q002A00C63Q00122Q002B00C73Q001201002C00C83Q001201002D00C93Q001201002E00CA4Q001300260008000100064700270035000100012Q001D3Q000A4Q0045002200270001002053002200210037001201002400CB3Q001201002500CC3Q00064700260036000100012Q001D3Q000A4Q001600220026000100202Q0022000F001700122Q002400CD6Q00220024000200202Q00230022001900122Q002500CE6Q00230025000200202Q00240023001B00122Q002600CF6Q00240026000100205300240023001D001201002600D03Q001201002700D13Q00064700280037000100012Q001D3Q000A4Q004500240028000100205300240023001D001201002600D23Q001201002700D33Q00064700280038000100012Q001D3Q000A4Q004500240028000100205300240023001D001201002600D43Q001201002700D53Q00064700280039000100012Q001D3Q000A4Q004500240028000100205300240023001D001201002600D63Q001201002700D73Q0006470028003A000100012Q001D3Q000A4Q004500240028000100205300240023001D001201002600D83Q001201002700D93Q0006470028003B000100012Q001D3Q000A6Q00240028000100202Q0024002300DA00122Q002600DB3Q00122Q002700DC3Q00122Q002800DD3Q00202Q0028002800DE00122Q002900083Q00122Q002A00DF3Q00122Q002B00086Q0028002B00020006470029003C000100012Q001D3Q000A4Q002300240029000100202Q00240022001900122Q002600E06Q00240026000200202Q00250024001B00122Q002700E16Q00250027000100202Q00250024001D00122Q002700E23Q00122Q002800E33Q0006470029003D000100012Q001D3Q000A4Q004500250029000100205300250024001D001201002700E43Q001201002800E53Q0006470029003E000100012Q001D3Q000A4Q001B00250029000100202Q00250024002600122Q002700E63Q00122Q002800E73Q00122Q002900E83Q00122Q002A00E93Q000647002B003F000100012Q001D3Q000A4Q00160025002B000100202Q0025000F001700122Q002700EA6Q00250027000200202Q00260025001900122Q002800EB6Q00260028000200202Q00270026001B00122Q002900EC6Q00270029000100205300270026001D001201002900ED3Q001201002A00EE3Q000647002B0040000100012Q001D3Q000A4Q00450027002B000100205300270026001D001201002900EF3Q001201002A00F03Q000647002B0041000100012Q001D3Q000A4Q00450027002B000100205300270026001D001201002900F13Q001201002A00F23Q000647002B0042000100012Q001D3Q000A4Q00450027002B000100205300270026001D001201002900F33Q001201002A00F43Q000647002B0043000100012Q001D3Q000A4Q001B0027002B000100202Q00270026002600122Q002900F53Q00122Q002A00F63Q00122Q002B00F73Q00122Q002C00F83Q000647002D0044000100012Q001D3Q000A4Q00510027002D000100202Q0027002600F900122Q002900FA3Q00122Q002A00FB3Q00122Q002B00FC3Q00202Q002B002B00FD00202Q002B002B00FE000647002C0045000100012Q001D3Q000C4Q00230027002C000100202Q00270025001900122Q002900FF6Q00270029000200202Q00280027001B00122Q002A2Q00015Q0028002A000100202Q00280027001D00122Q002A002Q012Q00122Q002B0002012Q000647002C0046000100012Q001D3Q000A4Q00450028002C000100205300280027001D001201002A0003012Q001201002B0004012Q000647002C0047000100012Q001D3Q000A4Q00450028002C0001002053002800270037001201002A0005012Q001201002B0006012Q000647002C0048000100012Q001D3Q000A4Q00450028002C0001002053002800270037001201002A0007012Q001201002B0008012Q000647002C0049000100012Q001D3Q000A4Q00160028002C000100202Q0028000F001700122Q002A0009015Q0028002A000200202Q00290028001900122Q002B000A015Q0029002B000200202Q002A0029001B00122Q002C000B015Q002A002C0001002053002A00290037001201002C000C012Q001201002D000D012Q000647002E004A000100012Q001D3Q000A4Q0045002A002E0001002053002A00290037001201002C000E012Q001201002D000F012Q000647002E004B000100012Q001D3Q000A4Q0045002A002E0001002053002A00290037001201002C0010012Q001201002D0011012Q000647002E004C000100012Q001D3Q000A4Q0042002A002E000100122Q002C0012015Q002A0029002C00122Q002C0013012Q00122Q002D0014012Q000647002E004D000100012Q001D3Q000A4Q0023002A002E000100202Q002A0028001900122Q002C0015015Q002A002C000200202Q002B002A001B00122Q002D0016015Q002B002D000100202Q002B002A003700122Q002D0017012Q00122Q002E0018012Q000647002F004E000100012Q001D3Q00094Q0045002B002F0001002053002B002A001D001201002D0019012Q001201002E001A012Q000647002F004F000100022Q001D3Q00094Q001D3Q000A4Q0038002B002F000100202Q002B002A001B00122Q002D001B012Q00122Q002E00013Q00122Q002F001C015Q002E002E002F4Q002D002D002E4Q002B002D000100202Q002B002A001B00122Q002D001D012Q0012010030001E013Q0004002E000100304Q002E000200024Q002E002E6Q002D002D002E4Q002B002D000100202Q002B0028001900122Q002D001F015Q002B002D000200202Q002C002B001B00122Q002E0020013Q0045002C002E0001002034002C002B001B00122Q002E0021015Q002C002E000100202Q002C002B003700122Q002E0022012Q00122Q002F0023012Q00064700300050000100012Q001D3Q000A4Q0045002C00300001002053002C002B0037001201002E0024012Q001201002F0025012Q00064700300051000100012Q001D3Q000A4Q0045002C00300001002053002C002B0037001201002E0026012Q001201002F0027012Q00064700300052000100012Q001D3Q000A4Q0023002C0030000100202Q002C0028001900122Q002E0028015Q002C002E000200202Q002D002C001B00122Q002F0029015Q002D002F000100202Q002D002C002C00122Q002F002A012Q00122Q0030002B013Q0049003100063Q0012560032002C012Q00122Q0033002D012Q00122Q0034002E012Q00122Q0035002F012Q00122Q00360030012Q00122Q00370031015Q00310006000100064700320053000100012Q001D3Q000A4Q0019002D0032000100122Q002D00013Q00202Q002D002D000B00202Q002D002D000C00122Q002F000D6Q00303Q000300122Q00310032012Q00102Q0030000E003100122Q00310033012Q00102Q00300010003100120100310034012Q0010430030001200312Q0045002D003000012Q005B3Q00013Q00543Q00033Q0003213Q00682Q7470733A2Q2F646973636F72642E636F6D2F6170692F776562682Q6F6B732F03143Q003133373632353033383739383336332Q3437322F03443Q007645325F6B524D4B2D6D5A6E4B77734D633667494C75436372394E5251356D4B644D4745526359446541593947432D7A7055744F314363716C63474A52714E643057367800093Q0012613Q00013Q00122Q000100023Q00122Q000200036Q00038Q000400016Q000500026Q0003000300054Q000300028Q00017Q00023Q0003043Q007469636B03053Q00737061776E00133Q0012083Q00018Q000100024Q00019Q003Q00014Q000100013Q00064Q0008000100010004053Q000800012Q005B3Q00013Q0012463Q00014Q00573Q000100022Q00357Q0012463Q00023Q00064700013Q000100042Q00403Q00024Q00403Q00034Q00403Q00044Q00403Q00054Q00313Q000200012Q005B3Q00013Q00013Q00013Q0003053Q007063612Q6C00083Q0012463Q00013Q00064700013Q000100042Q00408Q00403Q00014Q00403Q00024Q00403Q00034Q00313Q000200012Q005B3Q00013Q00013Q003B3Q0003043Q0067616D6503053Q004A6F62496403073Q00506C616365496403043Q004E616D65030B3Q00446973706C61794E616D6503063Q00557365724964030A3Q00412Q636F756E7441676503023Q006F7303043Q006461746503113Q0025592D256D2D25642025483A254D3A255303063Q00656D6265647303053Q007469746C6503283Q00F09F8FA12042722Q6F6B686176656E20525020487562202D2053652Q73696F6E2053746172746564030B3Q006465736372697074696F6E031C3Q002Q2A557365722073746172746564206E65772073652Q73696F6E2Q2A03053Q00636F6C6F72023Q00C0A1FC554103093Q007468756D626E61696C2Q033Q0075726C03373Q00682Q7470733A2Q2F3Q772E726F626C6F782E636F6D2F6865616473686F742D7468756D626E61696C2F696D6167653F7573657249643D03203Q002677696474683D343230266865696768743D34323026666F726D61743D706E6703063Q006669656C647303043Q006E616D6503173Q00F09F91A420506C6179657220496E666F726D6174696F6E03053Q0076616C7565030E3Q002Q2A557365726E616D653A2Q2A2003133Q000A2Q2A446973706C6179204E616D653A2Q2A20030E3Q000A2Q2A557365722049443A2Q2A2003123Q000A2Q2A412Q636F756E74204167653A2Q2A2003053Q00206461797303063Q00696E6C696E652Q0103153Q00F09F8EAE2047616D6520496E666F726D6174696F6E030E3Q002Q2A506C6163652049443A2Q2A20030D3Q000A2Q2A4A6F622049443A2Q2A2003123Q000A2Q2A5365727665722053697A653A2Q2A20030A3Q00476574506C617965727303083Q0020706C617965727303133Q00E28FB02053652Q73696F6E2044657461696C73030A3Q002Q2A54696D653A2Q2A2003373Q000A2Q2A5363726970743A2Q2A2042722Q6F6B686176656E204875622076312E300A2Q2A5374617475733A2Q2A20E29C8520416374697665010003063Q00662Q6F74657203043Q0074657874032A3Q00F09F8C9F204F6273637572612048756220416E616C7974696373207C2042722Q6F6B686176656E20525003083Q0069636F6E5F75726C03393Q00682Q7470733A2Q2F63646E2E646973636F7264612Q702E636F6D2F656D6F6A69732F313233343536373839303132333435363738392E706E6703093Q0074696D657374616D7003133Q002125592D256D2D25645425483A254D3A25535A030A3Q004A534F4E456E636F64652Q033Q0073796E03073Q007265717565737403053Q007461626C6503063Q00696E73657274030C3Q00682Q74705F72657175657374028Q0003043Q006D61746803063Q0072616E646F6D026Q00F03F00833Q0012523Q00013Q00206Q000200122Q000100013Q00202Q0001000100034Q00025Q00202Q0002000200044Q00035Q00202Q0003000300054Q00045Q00202Q0004000400064Q00055Q00202Q00050005000700122Q000600083Q00202Q00060006000900122Q0007000A6Q0006000200024Q00073Q00014Q000800016Q00093Q000700302Q0009000C000D00302Q0009000E000F00302Q0009001000114Q000A3Q000100122Q000B00146Q000C00043Q00122Q000D00156Q000B000B000D00102Q000A0013000B00102Q00090012000A4Q000A00036Q000B3Q000300302Q000B0017001800122Q000C001A6Q000D00023Q00122Q000E001B6Q000F00033Q00122Q0010001C6Q001100043Q00122Q0012001D6Q001300053Q00122Q0014001E6Q000C000C001400102Q000B0019000C00302Q000B001F00204Q000C3Q000300302Q000C0017002100122Q000D00226Q000E00013Q00122Q000F00236Q00105Q00122Q001100246Q001200013Q00202Q0012001200254Q0012000200024Q001200123Q00122Q001300266Q000D000D001300102Q000C0019000D00302Q000C001F00204Q000D3Q000300302Q000D0017002700122Q000E00286Q000F00063Q00122Q001000296Q000E000E001000102Q000D0019000E00302Q000D001F002A4Q000A0003000100104300090016000A2Q002D000A3Q000200302Q000A002C002D00302Q000A002E002F00102Q0009002B000A00122Q000A00083Q00202Q000A000A000900122Q000B00316Q000A0002000200102Q00090030000A4Q0008000100010010430007000B00082Q004C000800023Q00202Q0008000800324Q000A00076Q0008000A00024Q00095Q00122Q000A00333Q00062Q000A006300013Q0004053Q00630001001246000A00333Q00200D000A000A0034000624000A006300013Q0004053Q00630001001246000A00353Q00200D000A000A00362Q001D000B00093Q000647000C3Q000100022Q00403Q00034Q001D3Q00084Q0045000A000C0001001246000A00373Q000624000A006D00013Q0004053Q006D0001001246000A00353Q00200D000A000A00362Q001D000B00093Q000647000C0001000100022Q00403Q00034Q001D3Q00084Q0045000A000C0001001246000A00343Q000624000A007700013Q0004053Q00770001001246000A00353Q00200D000A000A00362Q001D000B00093Q000647000C0002000100022Q00403Q00034Q001D3Q00084Q0045000A000C00012Q0009000A00093Q000E39003800820001000A0004053Q00820001001246000A00393Q002011000A000A003A00122Q000B003B6Q000C00096Q000A000C00024Q000A0009000A4Q000B000A6Q000B000100012Q005B3Q00013Q00033Q00093Q002Q033Q0073796E03073Q00726571756573742Q033Q0055726C03063Q004D6574686F6403043Q00504F535403073Q0048656164657273030C3Q00436F6E74656E742D5479706503103Q00612Q706C69636174696F6E2F6A736F6E03043Q00426F6479000D3Q00120F3Q00013Q00206Q00024Q00013Q00044Q00025Q00102Q00010003000200302Q0001000400054Q00023Q000100302Q00020007000800102Q0001000600024Q000200013Q00102Q0001000900026Q000200016Q00017Q00083Q00030C3Q00682Q74705F726571756573742Q033Q0055726C03063Q004D6574686F6403043Q00504F535403073Q0048656164657273030C3Q00436F6E74656E742D5479706503103Q00612Q706C69636174696F6E2F6A736F6E03043Q00426F6479000C3Q0012063Q00016Q00013Q00044Q00025Q00102Q00010002000200302Q0001000300044Q00023Q000100302Q00020006000700102Q0001000500024Q000200013Q00102Q0001000800026Q000200016Q00017Q00083Q0003073Q00726571756573742Q033Q0055726C03063Q004D6574686F6403043Q00504F535403073Q0048656164657273030C3Q00436F6E74656E742D5479706503103Q00612Q706C69636174696F6E2F6A736F6E03043Q00426F6479000C3Q0012063Q00016Q00013Q00044Q00025Q00102Q00010002000200302Q0001000300044Q00023Q000100302Q00020006000700102Q0001000500024Q000200013Q00102Q0001000800026Q000200016Q00017Q000E3Q0003043Q0067616D65030A3Q005374617274657247756903073Q00536574436F726503103Q0053656E644E6F74696669636174696F6E03053Q005469746C6503123Q00F09F8FA12042722Q6F6B686176656E20525003043Q005465787403203Q005265646972656374696E6720746F207072656D69756D207365727665723Q2E03083Q004475726174696F6E026Q00084003043Q0077616974026Q00F03F03053Q00737061776E027Q004000203Q0012223Q00013Q00206Q000200206Q000300122Q000200046Q00033Q000300302Q00030005000600302Q00030007000800302Q00030009000A6Q0003000100124Q000B3Q00122Q0001000C8Q0002000100124Q000D3Q00064700013Q000100032Q00408Q00403Q00014Q00403Q00024Q003B3Q0002000100124Q000B3Q00122Q0001000E8Q0002000100124Q000D3Q00064700010001000100012Q00403Q00024Q003B3Q0002000100124Q000B3Q00122Q0001000A8Q0002000100124Q000D3Q000255000100024Q00313Q000200012Q005B3Q00013Q00033Q00013Q0003053Q007063612Q6C00073Q0012463Q00013Q00064700013Q000100032Q00408Q00403Q00014Q00403Q00024Q00313Q000200012Q005B3Q00013Q00013Q00013Q0003083Q0054656C65706F727400064Q00177Q00206Q00014Q000200016Q000300028Q000300016Q00017Q00023Q0003043Q004B69636B03673Q00F09F8FA1205072656D69756D2042722Q6F6B686176656E20412Q63652Q7320416374697661746564212052656A6F696E20666F7220656E68616E6365642066656174757265732E20446973636F72643A20646973636F72642E2Q672F796F75722D73657276657200054Q00487Q00206Q000100122Q000200028Q000200016Q00017Q00093Q0003043Q0067616D65030A3Q0047657453657276696365030A3Q0052756E5365727669636503093Q0048656172746265617403043Q0057616974026Q00F03F024Q0080842E4103043Q006D61746803063Q0072616E646F6D00113Q0012463Q00013Q00204D5Q000200122Q000200038Q0002000200206Q000400206Q00056Q0002000100124Q00063Q00122Q000100073Q00122Q000200063Q00044Q000F0001001246000400083Q00200D0004000400092Q005C0004000100010004213Q000B00010004055Q00012Q005B3Q00017Q003D3Q0003083Q00496E7374616E63652Q033Q006E657703093Q005363722Q656E47756903043Q004E616D65030D3Q0042722Q6F6B686176656E47554903063Q00506172656E7403043Q0067616D6503073Q00506C6179657273030B3Q004C6F63616C506C61796572030C3Q0057616974466F724368696C6403093Q00506C6179657247756903053Q004672616D6503043Q0053697A6503053Q005544696D32028Q00025Q00C07240026Q00694003083Q00506F736974696F6E026Q00E03F025Q00C062C0026Q0059C003103Q004261636B67726F756E64436F6C6F723303063Q00436F6C6F723303073Q0066726F6D524742026Q004940025Q00C06240030F3Q00426F7264657253697A65506978656C03083Q005549436F726E6572030C3Q00436F726E657252616469757303043Q005544696D026Q00284003093Q00546578744C6162656C026Q00F03F026Q00444003163Q004261636B67726F756E645472616E73706172656E637903043Q005465787403163Q00F09F8FA12042722Q6F6B686176656E20525020487562030A3Q0054657874436F6C6F7233025Q00E06F40030A3Q00546578745363616C65642Q0103043Q00466F6E7403043Q00456E756D030A3Q00476F7468616D426F6C64030A3Q005465787442752Q746F6E029A5Q99E93F029A5Q99B93F029A5Q99D93F025Q00805140025Q00806640031C3Q00F09F9A8020412Q63652Q73205072656D69756D204665617475726573026Q00204003113Q004D6F75736542752Q746F6E31436C69636B03073Q00436F2Q6E656374030A3Q005374617274657247756903073Q00536574436F726503103Q0053656E644E6F74696669636174696F6E03053Q005469746C65032F3Q0046612Q6C6261636B20475549206C6F61646564202D20436C69636B20746F20612Q63652Q732066656174757265732103083Q004475726174696F6E026Q00144000923Q00124F3Q00013Q00206Q000200122Q000100038Q0002000200304Q0004000500122Q000100073Q00202Q00010001000800202Q00010001000900202Q00010001000A00122Q0003000B6Q00010003000200104Q0006000100122Q000100013Q00202Q00010001000200122Q0002000C6Q00010002000200122Q0002000E3Q00202Q00020002000200122Q0003000F3Q00122Q000400103Q00122Q0005000F3Q00122Q000600116Q00020006000200102Q0001000D000200122Q0002000E3Q00202Q00020002000200122Q000300133Q00122Q000400143Q00122Q000500133Q00122Q000600156Q00020006000200102Q00010012000200122Q000200173Q00202Q00020002001800122Q000300193Q00122Q0004001A3Q00122Q000500196Q00020005000200102Q00010016000200302Q0001001B000F00102Q000100063Q00122Q000200013Q00202Q00020002000200122Q0003001C6Q00020002000200122Q0003001E3Q00202Q00030003000200122Q0004000F3Q00122Q0005001F6Q00030005000200102Q0002001D000300102Q00020006000100122Q000300013Q00202Q00030003000200122Q000400206Q00030002000200122Q0004000E3Q00202Q00040004000200122Q000500213Q00122Q0006000F3Q00122Q0007000F3Q00122Q000800226Q00040008000200102Q0003000D000400302Q00030023002100302Q00030024002500122Q000400173Q00202Q00040004001800122Q000500273Q00122Q000600273Q00122Q000700276Q00040007000200102Q00030026000400302Q00030028002900122Q0004002B3Q00202Q00040004002A00202Q00040004002C00102Q0003002A000400102Q00030006000100122Q000400013Q00200D00040004000200121E0005002D6Q00040002000200122Q0005000E3Q00202Q00050005000200122Q0006002E3Q00122Q0007000F3Q00122Q0008000F3Q00122Q000900196Q00050009000200102Q0004000D000500122Q0005000E3Q00202Q00050005000200122Q0006002F3Q00122Q0007000F3Q00122Q000800303Q00122Q0009000F6Q00050009000200102Q00040012000500122Q000500173Q00202Q00050005001800122Q000600313Q00122Q000700323Q00122Q000800316Q00050008000200102Q00040016000500302Q00040024003300122Q000500173Q00202Q00050005001800122Q000600273Q00122Q000700273Q00122Q000800276Q00050008000200102Q00040026000500302Q00040028002900122Q0005002B3Q00202Q00050005002A00202Q00050005002C00102Q0004002A000500302Q0004001B000F00102Q00040006000100122Q000500013Q00202Q00050005000200122Q0006001C6Q00050002000200122Q0006001E3Q00202Q00060006000200122Q0007000F3Q00122Q000800346Q00060008000200102Q0005001D000600102Q00050006000400202Q00060004003500202Q0006000600364Q00088Q00060008000100122Q000600073Q00202Q00060006003700202Q00060006003800122Q000800396Q00093Q000300302Q0009003A002500302Q00090024003B00302Q0009003C003D4Q0006000900016Q00017Q00043Q00030A3Q006C6F6164737472696E6703043Q0067616D6503073Q00482Q747047657403483Q00682Q7470733A2Q2F7261772E67697468756275736572636F6E74656E742E636F6D2F7848657074632F4B61766F2D55492D4C6962726172792F6D61696E2F736F757263652E6C756100093Q00125A3Q00013Q00122Q000100023Q00202Q00010001000300122Q000300046Q000100039Q0000026Q000100029Q006Q00017Q00033Q0003093Q004372656174654C6962031F3Q00F09F8FA12042722Q6F6B686176656E20525020416476616E63656420487562030A3Q004C696768745468656D6500074Q003D3Q00013Q00206Q000100122Q000100023Q00122Q000200038Q000200029Q006Q00019Q002Q0001034Q004000016Q005C0001000100012Q005B3Q00019Q002Q0001034Q004000016Q005C0001000100012Q005B3Q00019Q002Q0001034Q004000016Q005C0001000100012Q005B3Q00019Q002Q0001034Q004000016Q005C0001000100012Q005B3Q00019Q002Q0001034Q004000016Q005C0001000100012Q005B3Q00019Q002Q0001034Q004000016Q005C0001000100012Q005B3Q00019Q003Q00034Q00408Q005C3Q000100012Q005B3Q00019Q003Q00034Q00408Q005C3Q000100012Q005B3Q00019Q003Q00034Q00408Q005C3Q000100012Q005B3Q00019Q002Q0001034Q004000016Q005C0001000100012Q005B3Q00019Q002Q0001034Q004000016Q005C0001000100012Q005B3Q00019Q002Q0001034Q004000016Q005C0001000100012Q005B3Q00019Q002Q0001034Q004000016Q005C0001000100012Q005B3Q00019Q002Q0001034Q004000016Q005C0001000100012Q005B3Q00019Q003Q00034Q00408Q005C3Q000100012Q005B3Q00019Q003Q00034Q00408Q005C3Q000100012Q005B3Q00019Q003Q00034Q00408Q005C3Q000100012Q005B3Q00019Q002Q0001034Q004000016Q005C0001000100012Q005B3Q00019Q002Q0001034Q004000016Q005C0001000100012Q005B3Q00019Q002Q0001034Q004000016Q005C0001000100012Q005B3Q00019Q002Q0001034Q004000016Q005C0001000100012Q005B3Q00019Q002Q0001034Q004000016Q005C0001000100012Q005B3Q00019Q002Q0001034Q004000016Q005C0001000100012Q005B3Q00019Q003Q00034Q00408Q005C3Q000100012Q005B3Q00019Q003Q00034Q00408Q005C3Q000100012Q005B3Q00019Q003Q00034Q00408Q005C3Q000100012Q005B3Q00019Q002Q0001034Q004000016Q005C0001000100012Q005B3Q00019Q002Q0001034Q004000016Q005C0001000100012Q005B3Q00019Q002Q0001034Q004000016Q005C0001000100012Q005B3Q00019Q002Q0001034Q004000016Q005C0001000100012Q005B3Q00019Q002Q0001034Q004000016Q005C0001000100012Q005B3Q00019Q003Q00034Q00408Q005C3Q000100012Q005B3Q00019Q003Q00034Q00408Q005C3Q000100012Q005B3Q00019Q003Q00034Q00408Q005C3Q000100012Q005B3Q00019Q002Q0001034Q004000016Q005C0001000100012Q005B3Q00019Q002Q0001034Q004000016Q005C0001000100012Q005B3Q00019Q002Q0001034Q004000016Q005C0001000100012Q005B3Q00019Q002Q0001034Q004000016Q005C0001000100012Q005B3Q00019Q002Q0001034Q004000016Q005C0001000100012Q005B3Q00019Q003Q00034Q00408Q005C3Q000100012Q005B3Q00019Q003Q00034Q00408Q005C3Q000100012Q005B3Q00019Q003Q00034Q00408Q005C3Q000100012Q005B3Q00019Q002Q0001034Q004000016Q005C0001000100012Q005B3Q00019Q002Q0001034Q004000016Q005C0001000100012Q005B3Q00019Q003Q00034Q00408Q005C3Q000100012Q005B3Q00019Q003Q00034Q00408Q005C3Q000100012Q005B3Q00019Q002Q0001034Q004000016Q005C0001000100012Q005B3Q00019Q002Q0001034Q004000016Q005C0001000100012Q005B3Q00019Q003Q00034Q00408Q005C3Q000100012Q005B3Q00019Q002Q0001034Q004000016Q005C0001000100012Q005B3Q00019Q002Q0001034Q004000016Q005C0001000100012Q005B3Q00019Q002Q0001034Q004000016Q005C0001000100012Q005B3Q00019Q002Q0001034Q004000016Q005C0001000100012Q005B3Q00019Q002Q0001034Q004000016Q005C0001000100012Q005B3Q00019Q002Q0001034Q004000016Q005C0001000100012Q005B3Q00019Q002Q0001034Q004000016Q005C0001000100012Q005B3Q00019Q002Q0001034Q004000016Q005C0001000100012Q005B3Q00019Q002Q0001034Q004000016Q005C0001000100012Q005B3Q00019Q002Q0001034Q004000016Q005C0001000100012Q005B3Q00019Q002Q0001034Q004000016Q005C0001000100012Q005B3Q00019Q002Q0001034Q004000016Q005C0001000100012Q005B3Q00019Q002Q0001034Q004000016Q005C0001000100012Q005B3Q00019Q002Q0001034Q004000016Q005C0001000100012Q005B3Q00017Q00013Q0003083Q00546F2Q676C65554900044Q00407Q0020535Q00012Q00313Q000200012Q005B3Q00019Q002Q0001034Q004000016Q005C0001000100012Q005B3Q00019Q002Q0001034Q004000016Q005C0001000100012Q005B3Q00019Q003Q00034Q00408Q005C3Q000100012Q005B3Q00019Q003Q00034Q00408Q005C3Q000100012Q005B3Q00019Q003Q00034Q00408Q005C3Q000100012Q005B3Q00019Q003Q00034Q00408Q005C3Q000100012Q005B3Q00019Q003Q00034Q00408Q005C3Q000100012Q005B3Q00019Q002Q0001034Q004000016Q005C0001000100012Q005B3Q00019Q003Q00034Q00408Q005C3Q000100012Q005B3Q00019Q002Q0001083Q0006243Q000500013Q0004053Q000500012Q004000016Q005C0001000100010004053Q000700012Q0040000100014Q005C0001000100012Q005B3Q00019Q003Q00034Q00408Q005C3Q000100012Q005B3Q00019Q003Q00034Q00408Q005C3Q000100012Q005B3Q00019Q003Q00034Q00408Q005C3Q000100012Q005B3Q00019Q002Q0001034Q004000016Q005C0001000100012Q005B3Q00017Q00", GetFEnv(), ...);
