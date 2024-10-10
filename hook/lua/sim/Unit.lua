-- WARN('['..string.gsub(debug.getinfo(1).source, ".*\\(.*.lua)", "%1")..', line:'..debug.getinfo(1).currentline..'] * QUIET Hook for Unit.lua' ) 
-- This warning allows us to see exactly where our Hook Line starts so we can debug the exact line thats causing an error easier

-- Hook
-- Reason: Adjusting overkillRatio from 0.10 to 0.30 to allow more Wreckage to be created even if there large overkill, I.E T4 AA shooting down T2 Gunships.
QCEUnit = Unit
Unit = Class(QCEUnit) {

    DoTakeDamage = function(self, instigator, amount, vector, damageType)

		local GetHealth = GetHealth
	
        local preAdjHealth = GetHealth(self)
		
        AdjustHealth( self, instigator, -amount)
		
        if GetHealth(self) < 1 then
		
            if damageType == 'Reclaimed' then
			
                self:Destroy()
				
            else
			
                local excessDamageRatio = 0.0
				
                -- Calculate the excess damage amount
                local excess = preAdjHealth - amount
                local maxHealth = EntityMethods.GetMaxHealth(self)
				
                if (excess < 0 and maxHealth > 0) then
				
                    excessDamageRatio = -excess / maxHealth
					
                end
				
                Kill( self, instigator, damageType, excessDamageRatio)
				
            end
			
        end

        -- Handle incoming OC damage for ACUs
        if damageType == 'Overcharge' and LOUDENTITY(categories.COMMAND, self) then

            local wep = instigator:GetWeaponByLabel('OverCharge')

            amount = wep:GetBlueprint().Overcharge.commandDamage
            
        end

        -- Handle incoming OC damage for Structures
        if damageType == 'Overcharge' and LOUDENTITY(categories.STRUCTURE, self) then

            local wep = instigator:GetWeaponByLabel('OverCharge')

            amount = wep:GetBlueprint().Overcharge.structureDamage
            
        end
		
		
        if not self.Dead and LOUDENTITY(categories.COMMAND, self) then
		
			GetAIBrain(self):OnPlayCommanderUnderAttackVO()
			
        end
		
    end,

    ReduceTransportSpeed = function(self)
        local bp = self:GetBlueprint()
        local transportspeed = bp.Air.MaxAirspeed
        local totalweight = 0
        for _, unit in self:GetCargo() do
            if unit and unit:GetBlueprint() then
                local bp = unit:GetBlueprint()
                totalweight = totalweight + bp.Physics.TransportSpeedReduction
	        else
                WARN("Unit or its blueprint is nil.")
            end
        end
        self:SetSpeedMult(1 - (totalweight / transportspeed))
        --LOG("Transport Speed is "..repr((1 - (totalweight / transportspeed))))
    end,

    -- issued by the Transport as a unit loads on
    OnTransportAttach = function(self, attachBone, unit)
    
        --LOG("*AI DEBUG Transport "..self.Sync.id.." attaches unit "..unit.Sync.id.." on tick "..GetGameTick() )

        self:MarkWeaponsOnTransport(unit, true)
		
        if unit:ShieldIsOn() then
            unit:DisableShield()
            unit:DisableDefaultToggleCaps()
        end
		
		unit:SetDoNotTarget(true)
        unit:SetCanTakeDamage(false)
		
        if not LOUDENTITY(categories.PODSTAGINGPLATFORM, self) then
            self:RequestRefreshUI()
        end

        unit:DoUnitCallbacks( 'OnAttachedToTransport', self )
		
        self:DoUnitCallbacks('OnTransportAttach', unit )

        self:ReduceTransportSpeed()
		
    end,

	-- issued by the Transport as units are detached
    OnTransportDetach = function(self, attachBone, unit)

        --LOG("*AI DEBUG Transport "..self.Sync.id.." detaches unit "..unit.Sync.id.." on tick "..GetGameTick() )

        self:MarkWeaponsOnTransport(unit, false)
		
		if not unit:ShieldIsOn() then
			unit:EnableShield()
			unit:EnableDefaultToggleCaps()
		end
		
		unit:SetDoNotTarget(false)
        unit:SetCanTakeDamage(true)

        if not LOUDENTITY(categories.PODSTAGINGPLATFORM, self) then
            self:RequestRefreshUI()
        end
		
        unit:TransportAnimation(-1)

        unit:DoUnitCallbacks( 'OnDetachedToTransport', self)
		
        self:DoUnitCallbacks('OnTransportDetach', unit )

        self:ReduceTransportSpeed()
		
    end,

    DeathThread = function( self, overkillRatio, instigator)

        if self.DeathAnimManip then
            WaitFor(self.DeathAnimManip)
        end

        self.PlayUnitSound(self,'Destroyed')		
        
        local waitTime = self.DeathThreadDestructionWaitTime or 0.1
        local function createEffects()
            if self.DamageEffectsBag then
                self:DestroyAllDamageEffects()
            end

            -- if simspeed too low suppress destruction effects --
            if Sync.SimData.SimSpeed > -1 then
        
                if self.PlayDestructionEffects then
                    self:CreateDestructionEffects( overkillRatio )
                end
        
                if ( self.ShowUnitDestructionDebris and overkillRatio ) then
        
                    if overkillRatio <= 0.30 then
                        self:CreateUnitDestructionDebris( true, true, false )
                    else
                        self:CreateUnitDestructionDebris( false, true, true )
                    end
                end
            end
        end

        local function createWreckage()
            if overkillRatio <= 0.30 then
                self:CreateWreckage( overkillRatio )
            end
        end

        ForkThread(function()
            WaitTicks(waitTime * 10)
            createEffects()
            createWreckage()
            self:Destroy()
        end)
    end,

}