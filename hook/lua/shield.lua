-- WARN('['..string.gsub(debug.getinfo(1).source, ".*\\(.*.lua)", "%1")..', line:'..debug.getinfo(1).currentline..'] * QUIET Hook for Shield.lua' ) 
-- This warning allows us to see exactly where our Hook Line starts so we can debug the exact line thats causing an error easier

--  /lua/shield.lua
-- Added support for hunker shields

do -- encasing the code in do .... end means that you dont have to worry about using unique variables


local Entity = import('/lua/sim/Entity.lua').Entity
local EffectTemplate = import('/lua/EffectTemplates.lua')

local shieldAbsorptionValues = import("/mods/QUIET-Community-Edition/lua/ShieldAbsorptionValues.lua").shieldAbsorptionValues

local ChangeState = ChangeState

local LOUDENTITY    = EntityCategoryContains
local LOUDMAX       = math.max
local LOUDMIN       = math.min
local LOUDPARSE     = ParseEntityCategory	
local LOUDPOW       = math.pow
local LOUDSQRT      = math.sqrt

local TableAssimilate = table.assimilate

-- cache globals
local Warp = Warp
local IsEntity = IsEntity
local IsAlly = IsAlly
local IsEnemy = IsEnemy
local Random = Random
local GetGameTick = GetGameTick
local ForkThread = ForkThread
local ChangeState = ChangeState
local ArmyGetHandicap = ArmyGetHandicap
local CoroutineYield = coroutine.yield
local CreateEmitterAtBone = CreateEmitterAtBone
local _c_CreateShield = _c_CreateShield

-- cache trashbag functions
local TrashBag = TrashBag
local TrashAdd = TrashBag.Add
local TrashDestroy = TrashBag.Destroy
local WaitTicks     = coroutine.yield
local Warp          = Warp

local ForkThread = ForkThread
local ForkTo = ForkThread

local IsEnemy = IsEnemy
local KillThread = KillThread

local CreateEmitterAtBone = CreateEmitterAtBone

local VectorCached = { 0, 0, 0 }
	
local AdjustHealth      = moho.entity_methods.AdjustHealth
local GetArmy           = moho.entity_methods.GetArmy        
local GetBlueprint      = moho.entity_methods.GetBlueprint
local GetHealth         = moho.entity_methods.GetHealth
local GetMaxHealth      = moho.entity_methods.GetMaxHealth
local SetMesh           = moho.entity_methods.SetMesh

local GetArmorMult      = moho.unit_methods.GetArmorMult
local GetStat           = moho.unit_methods.GetStat
local SetStat           = moho.unit_methods.SetStat
local SetShieldRatio    = moho.unit_methods.SetShieldRatio

local EntityGetHealth = moho.entity_methods.GetHealth
local EntityGetMaxHealth = moho.entity_methods.GetMaxHealth
local EntitySetHealth = moho.entity_methods.SetHealth
local EntitySetMaxHealth = moho.entity_methods.SetMaxHealth
local EntityAdjustHealth = moho.entity_methods.AdjustHealth
local EntityGetArmy = moho.entity_methods.GetArmy
local EntityGetEntityId = moho.entity_methods.GetEntityId
local EntitySetVizToFocusPlayer = moho.entity_methods.SetVizToFocusPlayer
local EntitySetVizToEnemies = moho.entity_methods.SetVizToEnemies
local EntitySetVizToAllies = moho.entity_methods.SetVizToAllies
local EntitySetVizToNeutrals = moho.entity_methods.SetVizToNeutrals
local EntityAttachBoneTo = moho.entity_methods.AttachBoneTo
local EntityGetPosition = moho.entity_methods.GetPosition
local EntityGetPositionXYZ = moho.entity_methods.GetPositionXYZ
local EntitySetMesh = moho.entity_methods.SetMesh
local EntitySetDrawScale = moho.entity_methods.SetDrawScale
local EntitySetOrientation = moho.entity_methods.SetOrientation
local EntityDestroy = moho.entity_methods.Destroy
local EntityBeenDestroyed = moho.entity_methods.BeenDestroyed
local EntitySetCollisionShape = moho.entity_methods.SetCollisionShape

local EntitySetParentOffset = moho.entity_methods.SetParentOffset

local UnitSetScriptBit = moho.unit_methods.SetScriptBit
local UnitIsUnitState = moho.unit_methods.IsUnitState
local UnitRevertCollisionShape = moho.unit_methods.RevertCollisionShape

local IEffectOffsetEmitter = moho.IEffect.OffsetEmitter

local CategoriesOverspill = categories.SHIELD * categories.DEFENSE

LargestShieldDiameter = 0
for k, bp in __blueprints do
    -- check for blueprints that have a shield and a shield size set
    if bp.Defense and bp.Defense.Shield and bp.Defense.Shield.ShieldSize then
        -- skip Aeon palace and UEF shield boat as they skew the results
        if not (bp.BlueprintId == "xac2101" or bp.BlueprintId == "xes0205") then
            local size = bp.Defense.Shield.ShieldSize
            if size > LargestShieldDiameter then
                LargestShieldDiameter = size
            end
        end
    end
end

QCEShield = Shield
Shield = Class(QCEShield) {

    RemainEnabledWhenAttached = false,
    --LOG("We've entered LCE Version of Shield.lua"),

    __init = function(self, spec)
        _c_CreateShield(self, spec)
    end,

    OnCreate = function(self, spec)
        -- cache information that is used frequently
        self.Army = EntityGetArmy(self)
        self.EntityId = EntityGetEntityId(self)
        self.Brain = spec.Owner:GetAIBrain()
        self.Dead = false

        if spec.ImpactEffects ~= '' then
			self.ImpactEffects = EffectTemplate[spec.ImpactEffects]
		else
			self.ImpactEffects = false
		end
        
        if spec.ImpactMesh ~= '' then
            self.ImpactMeshBp = spec.ImpactMesh
        else
            self.ImpactMeshBp = false
        end

        -- manage impact entities
        self.ImpactEntitySpecs = { Owner = spec.Owner }
        self.LiveImpactEntities = 0

        -- manage overlapping shields
        self.OverlappingShields = {}
        self.OverlappingShieldsCount = 0
        self.OverlappingShieldsTick = -1

        -- manage overspill
        self.DamagedTick = {}
        self.DamagedRegular = {}
        self.DamagedOverspill = {}

        -- set some internal state related to shields
        self._IsUp = false
        self.ShieldType = 'Bubble'

        -- copy over information from specification
        self.Size = spec.Size
        self.Owner = spec.Owner
        self.MeshBp = spec.Mesh
        self.MeshZBp = spec.MeshZ
        self.SpillOverDmgMod = spec.ShieldSpillOverDamageMod or 0.15
        self.ShieldRechargeTime = spec.ShieldRechargeTime or 5
        self.ShieldEnergyDrainRechargeTime = spec.ShieldEnergyDrainRechargeTime or 5
        self.ShieldVerticalOffset = spec.ShieldVerticalOffset or -1
        self.PassOverkillDamage = spec.PassOverkillDamage
        self.SkipAttachmentCheck = spec.SkipAttachmentCheck
        self.AbsorptionType = spec.AbsorptionType
        self.AbsorptionTypeDamageTypeToMulti = shieldAbsorptionValues[self.AbsorptionType or "Default"]

        -- use trashbag of the unit that owns us
        self.Trash = self.Owner.Trash

        -- set our health
        EntitySetMaxHealth(self, spec.ShieldMaxHealth)
        EntitySetHealth(self, self, spec.ShieldMaxHealth)

        SetShieldRatio(self.Owner, 1)

        self:SetShieldRegenRate(spec.ShieldRegenRate)
        self:SetShieldRegenStartTime(spec.ShieldRegenStartTime)

        -- tell the engine when we should be visible
        EntitySetVizToFocusPlayer(self, 'Always')
        EntitySetVizToEnemies(self, 'Intel')
        EntitySetVizToAllies(self, 'Always')
        EntitySetVizToNeutrals(self, 'Intel')

        -- attach us to the owner
        EntityAttachBoneTo(self, -1, spec.Owner, -1)

        if ScenarioInfo.ShieldDialog then
            LOG("*AI DEBUG Shield created on " .. __blueprints[self.Owner.BlueprintID].Description)
        end

        ChangeState(self, self.EnergyDrainRechargeState)
    end,
	
    -- Create a new thread and fork it. Also add it to the unit's trashbag so it gets cleaned up when the unit dies.
    ForkThread = function(self, fn, ...)
        local thread = ForkThread(fn, self, unpack(arg))
        TrashAdd( self.Owner.Trash, thread )
		return thread
    end,

    -- Set the recharge time and energy recharge time for this shield.
    SetRechargeTime = function(self, rechargeTime, energyRechargeTime)
        self.ShieldRechargeTime = rechargeTime
        self.ShieldEnergyDrainRechargeTime = energyRechargeTime
    end,

    -- Set the vertical offset for this shield.
    SetVerticalOffset = function(self, offset)
        self.ShieldVerticalOffset = offset
    end,

    -- Set the size of this shield.
    SetSize = function(self, size)
        self.Size = size
    end,

    -- Set the shield regen rate.
    SetShieldRegenRate = function(self, rate)
        self.RegenRate = rate
    end,

    -- Set the shield regen start time.
    SetShieldRegenStartTime = function(self, time)
        self.RegenStartTime = time
    end,

    -- Update the shield ratio for the unit. If value is negative, calculate it from the current health of the shield.
    UpdateShieldRatio = function(self, value)
	
        if value < 0 then
            value = EntityGetHealth(self) / EntityGetMaxHealth(self)
        end
		
        SetShieldRatio( self.Owner, value )
    end,

    -- Get the position of the shield, this is the same as the unit's position.
    GetCachePosition = function(self)
        return self:GetPosition()
    end,

    -- Called by native code to calculate spillover damage. Native code will subtract
    -- the returned value from any damage it does to units under the shield. The
    -- default is to always absorb as much as possible but the reason this function
    -- exists is to allow flexible implementations like shields that only absorb
    -- partial damage (like armor). Performance-sensitive as it's called on every
    -- damage event.
    --- How much of incoming damage is absorbed by the shield. Used by the engine to calculate remainder spillover damage
    ---@param self Shield
    ---@param instigator Unit
    ---@param amount number
    ---@param type DamageType
    ---@return number damageAbsorbed If not all damage is absorbed, the remainder passes to targets under the shield.
    OnGetDamageAbsorption = function(self, instigator, amount, type)
        -- We don't absorb tree damage
        if type == "TreeForce" or type == "TreeFire" then
            return 0
        end

        -- Decouple shield absorption from owner armor
        local absorptionMulti = self.AbsorptionTypeDamageTypeToMulti[type] or self.Owner:GetArmorMult(type)

        -- First apply armor reduction, then apply handicap
        amount = amount * absorptionMulti
        amount = amount * (1.0 - ArmyGetHandicap(self.Army))

        local health = EntityGetHealth(self)
        return math.min(amount, health)
    end,

    --- Retrieves allied shields that overlap with this shield, caches the results per tick
    -- @param self A shield that we're computing the overlapping shields for
    -- @param tick Optional parameter, represents the game tick. Used to determine if we need to refresh the cash
    GetOverlappingShields = function(self, tick)

        -- allow the game tick to be send to us, saves cycles
        tick = tick or GetGameTick()

        -- see if we need to re-compute the overlapping shields as the information we're requesting is of a different tick
        if tick ~= self.OverlappingShieldsTick then
            self.OverlappingShieldsTick = tick

            local brain = self.Brain
            local position = EntityGetPosition(self.Owner)

            -- diameter where other shields overlap with us or are contained by us
            local diameter = LargestShieldDiameter + self.Size

            -- retrieve candidate units
            local units = brain:GetUnitsAroundPoint(CategoriesOverspill, position, 0.5 * diameter, 'Ally')

            if units then
<<<<<<< Updated upstream
                --LOG("We found overlapping shields "..repr(units))
=======
>>>>>>> Stashed changes
                -- allocate locals once
                local shieldOther
                local radiusOther
                local distanceToOverlap
                local osx, osy, osz
                local d, dx, dy, dz

                -- compute our information only once
                local psx, psy, psz = EntityGetPositionXYZ(self)
                local radius = 0.5 * self.Size

                -- pre-allocate our result table once to avoid allocating it every iteration
                -- and to avoid using the slow built-in table.insert
                local overlappingShields = {}
                local head = 1

                for k, other in units do

                    -- store reference to reduce table lookups
                    shieldOther = other.MyShield

                    -- check if it is a different unti and that it has an active shield with a radius
                    -- larger than 0, as engine defaults shield table to 0
                    if shieldOther
                        and shieldOther.ShieldType ~= "Personal"
                        and shieldOther:IsUp()
                        and shieldOther.Size
                        and shieldOther.Size > 0
                        and self.Owner.EntityId ~= other.EntityId
                    then

                        -- compute radius of shield
                        radiusOther = 0.5 * shieldOther.Size

                        -- compute total distance to overlap and square it to prevent a square root
                        distanceToOverlap = radius + radiusOther
                        distanceToOverlap = distanceToOverlap * distanceToOverlap

                        -- retrieve position of other shield
                        osx, osy, osz = EntityGetPositionXYZ(shieldOther)

                        -- compute vector from self to other
                        dx = osx - psx
                        dy = osy - psy
                        dz = osz - psz

                        -- compute squared distance and check it
                        d = dx * dx + dy * dy + dz * dz
                        if d < distanceToOverlap then
                            overlappingShields[head] = shieldOther
                            head = head + 1
                        end
                    end
                end
                -- keep track of the number of adjacent shields
                self.OverlappingShieldsCount = head - 1
<<<<<<< Updated upstream
=======
                self.OverlappingShields = overlappingShields
>>>>>>> Stashed changes
            else
                -- no units found
                self.OverlappingShieldsCount = 0
                self.OverlappingShields = {}
            end
        end
        -- return the shields in question
        return self.OverlappingShields, self.OverlappingShieldsCount
    end,

    -- Check if the shield should collide with the weapon
    -- This is used to prevent friendly fire, and to allow for DoNotCollideList to be used
    -- to prevent collision with certain units
    OnCollisionCheckWeapon = function(self, firingWeapon)
        -- Check if the shield and the unit firing the weapon are allies
        if IsAlly(self.Army, GetArmy(firingWeapon.unit)) then
            return false
        end

        -- Check DoNotCollideList
        local weaponBP = firingWeapon.bp
        if weaponBP.DoNotCollideList then
            -- Iterate over the DoNotCollideList, and if the shield matches any of the entities, return false
            local LOUDENTITY = LOUDENTITY
            local LOUDPARSE = LOUDPARSE
            for _, v in weaponBP.DoNotCollideList do
                if LOUDENTITY(LOUDPARSE(v), self) then
                    return false
                end
            end
        end

        -- If the shield does not match any of the entities in the DoNotCollideList, then return true
        return true
    end,
    
    GetOverkill = function(self,instigator,amount,type)
    end,    


    -- This function is called when a shield is directly impacted, excluding personal shields.
    -- It's also called from the ApplyDamage function when doOverspill is true.

    -- The main purpose of this function is to apply shield spill damage to other shields in the area.
    OnDamage = function(self, instigator, amount, vector, damageType)
        
        -- Only applies to trees. This is a special case for the tree force and tree fire damage types.
        -- It's not necessary to apply shield spill damage to trees, as they are not entities that can take damage.
        if damageType == "TreeForce" or damageType == "TreeFire" then
            return
        end

        -- Only called when a shield is directly impacted, so not for Personal Shields
        -- This means personal shields never have ApplyDamage called with doOverspill as true
        self:ApplyDamage(instigator, amount, vector, damageType, true)
    end,

    ApplyDamage = function(self, instigator, amount, vector, dmgType, doOverspill)
        -- cache information used throughout the function
        local tick = GetGameTick()
        local instigatorId = (instigator and instigator.EntityId) or false

        -- damage correction for overcharge
        -- These preset damages deal `2 * dmg * absorbMult or armorMult`, currently absorption multiplier is 1x so we need to divide by 2
        if dmgType == 'Overcharge' then
            local wep = instigator:GetWeaponByLabel('OverCharge')
            if self.StaticShield then -- fixed damage for static shields
                amount = wep:GetBlueprint().Overcharge.structureDamage / 2
            elseif self.CommandShield then -- fixed damage for UEF bubble shield
                amount = wep:GetBlueprint().Overcharge.commandDamage / 2
            end
        end

        -- damage correction for overspill, do not apply to personal shields
        if self.ShieldType ~= "Personal" then

            -- keep track of the damage we have received from this instigator at this tick
            if instigatorId then
                if self.DamagedTick[instigatorId] ~= tick then
                    self.DamagedTick[instigatorId] = tick
                    self.DamagedRegular[instigatorId] = false
                    self.DamagedOverspill[instigatorId] = 0
                end

                -- if we have already received regular damage from this instigator at this tick, skip the overspill damage
                if self.DamagedRegular[instigatorId] == tick then
                    return
                end

                -- keep track of overspill damage if we have not received any actual damage yet
                self.DamagedOverspill[instigatorId] = self.DamagedOverspill[instigatorId] + amount
            end
        end

        -- do damage logic for shield

        if self.Owner ~= instigator then
            local absorbed = self:OnGetDamageAbsorption(instigator, amount, dmgType)

            -- take some damage
            EntityAdjustHealth(self, instigator, -absorbed)

            -- check to spawn impact effect
            local r = Random(1, self.Size)
            if dmgType ~= "ShieldSpill"
                and not (self.LiveImpactEntities > 10
                    and (r >= 0.2 * self.Size and r < self.LiveImpactEntities))
            then
                ForkThread(self.CreateImpactEffect, self, vector)
            end

            if self.RegenThread then
                KillThread(self.RegenThread)
                self.RegenThread = nil
            end
             
            if GetHealth(self) <= 0 then
                ChangeState(self, self.DamageRechargeState)
            else
                if self.OffHealth < 0 then
                 
                    ForkTo(self.CreateImpactEffect, self, vector)
                     
                    if self.RegenRate > 0 then
                     
                        self.RegenThread = self:ForkThread(self.RegenStartThread)
     
                    end
                else
                    self:UpdateShieldRatio(0) 
                end
            end
        end

        -- overspill damage checks

        if -- prevent recursively applying overspill
        doOverspill
            -- personal shields do not have overspill damage
            and self.ShieldType ~= "Personal"
            -- we consider damage without an instigator irrelevant, typically force events
            and IsEntity(instigator)
            -- we consider damage that is 1 or lower irrelevant, typically force events
            and amount > 1
            -- do not recursively apply overspill damage
            and dmgType ~= "ShieldSpill"
        then
            local spillAmount = self.SpillOverDmgMod * amount

            -- retrieve shields that overlap with us
            local others, count = self:GetOverlappingShields(tick)

            -- apply overspill damage to neighbour shields
            for k = 1, count do
                others[k]:ApplyDamage(
                    instigator, -- instigator
                    spillAmount, -- amount
                    nil, -- vector
                    "ShieldSpill", -- type
                    false-- do overspill
                )
            end
        end
    end,

    RegenStartThread = function(self)
        -- this thread is responsible for regenerating the shield
        -- it takes a delay before starting to regenerate
        -- and will keep regenerating until the shield is full
        -- or the unit is destroyed
        -- it will also update the shield ratio for the owner unit
    
        local owner = self.Owner
        local GetHealth = GetHealth
        local GetMaxHealth = GetMaxHealth
        local SetShieldRatio = SetShieldRatio
        
        local function adjustHealthAndRatio(amount)
            -- helper function to adjust health and shield ratio
            AdjustHealth(self, owner, amount)
            SetShieldRatio(owner, GetHealth(self)/GetMaxHealth(self))
        end
        
        if ScenarioInfo.ShieldDialog then
            LOG("*AI DEBUG Shield Starts Regen Thread on "..repr(self.BlueprintID).." "..repr(__blueprints[self.BlueprintID].Description).." - start delay is "..repr(self.RegenStartTime) )
        end
        
        -- shield takes a delay before regen starts
        WaitTicks( 10 + (self.RegenStartTime * 10) )
        
        while not self.Dead and GetHealth(self) < GetMaxHealth(self) do
            -- regen the shield
            if not self.Dead then
                adjustHealthAndRatio(self.RegenRate)
                
                -- wait one second
                WaitTicks(11)
            end
        end
    end,

    CreateImpactEffect = function(self, vector)

        if IsDestroyed(self) then
            return
        end

        -- keep track of this entity
        self.LiveImpactEntities = self.LiveImpactEntities + 1

        -- cache values
        local effect
        local army = self.Army
        local vc = VectorCached

        -- compute distance to offset effect
        local x = vector[1]
        local y = vector[2]
        local z = vector[3]
        local d = LOUDSQRT(x * x + y * y + z * z)

        -- allocate an entity
        local entity = Entity(self.ImpactEntitySpecs)

        vc[1], vc[2], vc[3] = EntityGetPositionXYZ(self)
        Warp(entity, vc)

        -- set the impact mesh and scale it accordingly
        if self.ImpactMeshBp ~= '' then
            EntitySetMesh(entity, self.ImpactMeshBp)
            EntitySetDrawScale(entity, self.Size)

            vc[1], vc[2], vc[3] = -x, -y, -z
            EntitySetOrientation(entity, OrientFromDir(vc), true)
        end

        -- spawn additional effects
        for _, v in self.ImpactEffects do
            effect = CreateEmitterAtBone(entity, -1, army, v)
            IEffectOffsetEmitter(effect, 0, 0, d)
        end

        -- hold up a bit
        CoroutineYield(20)

        -- take out the entity again
        EntityDestroy(entity)

        self.LiveImpactEntities = self.LiveImpactEntities - 1
    end,

    -- called when the shield is destroyed
    OnDestroy = function(self)

        if self.RegenThread then
            -- kill the regen thread
            KillThread(self.RegenThread)
            self.RegenThread = nil
        end

        self:SetMesh('')
        
        if self.MeshZ != nil then
            -- remove the mesh used for the shield
            self.MeshZ:Destroy()
            self.MeshZ = nil
        end
        
        self:UpdateShieldRatio(0)
        
        self.Dead = true
        
        -- change state to dead
        ChangeState(self, self.DeadState)
    end,

    -- Return true to process this collision, false to ignore it.
    OnCollisionCheck = function(self,other)
	    -- if shield piercing and other is a shield piercing category
	    if categories.SHIELDPIERCING and LOUDENTITY(categories.SHIELDPIERCING, other) then
		    return false
	    end
		
        if other.LastImpact then
            -- if hit same unit twice
            if other.LastImpact == self.Owner.MyShield:GetEntityId() then
                return false
            end
        end

        -- if other is a railgun
	    if other.DamageData.DamageType == 'Railgun' then
		    other.LastImpact = self.Owner.MyShield:GetEntityId()
	    end
		
        -- return true if owner and other are enemies
        return IsEnemy(self.Army, GetArmy(other))
    end,

    TurnOn = function(self)
        ChangeState(self, self.OnState)
    end,

    TurnOff = function(self)
        ChangeState(self, self.OffState)
    end,

    IsOn = function(self)
        return false
    end,

    IsUp = function(self)
        return (self:IsOn() and self.Enabled)
    end,

    RemoveShield = function(self)
        self._IsUp = false
	
        self:SetCollisionShape('None')

		self:SetMesh('')
		
		if self.MeshZ != nil then
			self.MeshZ:Destroy()
			self.MeshZ = nil
		end

        self.Owner:OnShieldIsDown()
		
    end,

    CreateShieldMesh = function(self)
        
        local vec = VectorCached
        vec[1] = 0
        vec[2] = self.ShieldVerticalOffset
        vec[3] = 0
		
		self:SetParentOffset( vec )	

		self:SetCollisionShape( 'Sphere', 0, 0, 0, self.Size/2)

		self:SetMesh(self.MeshBp)

		self:SetDrawScale(self.Size)

		if self.MeshZ == nil then
		
			self.MeshZ = Entity { }

            Warp( self.MeshZ, self.Owner:GetPosition() )			

			self.MeshZ:AttachBoneTo(-1,self.Owner,-1)

            vec[1] = 0
            vec[2] = self.ShieldVerticalOffset
            vec[3] = 0
            
			self.MeshZ:SetParentOffset( vec )

			self.MeshZ:SetMesh(self.MeshZBp)

			self.MeshZ:SetDrawScale(self.Size)

			self.MeshZ:SetVizToFocusPlayer('Always')
			self.MeshZ:SetVizToEnemies('Intel')
			self.MeshZ:SetVizToAllies('Always')
			self.MeshZ:SetVizToNeutrals('Intel')
		end
		
        self.Owner:OnShieldIsUp()
        self._IsUp = true
    end,

    -- Basically run a timer, but with a visual bar
	-- The time value is in seconds but the charging up period can be slowed if resources are not available
    ChargingUp = function(self, curProgress, time)
	
        self.Owner:OnShieldIsCharging()
    
		local GetResourceConsumed = moho.unit_methods.GetResourceConsumed
		local SetShieldRatio = SetShieldRatio
		local WaitTicks = WaitTicks
        
        while not self.Dead and curProgress < time do
			
            curProgress = curProgress + GetResourceConsumed( self.Owner )
			
			SetShieldRatio( self.Owner, curProgress/time )
			
            WaitTicks(11)
        end    
    end,

    OnState = State {
	
        Main = function(self)
		
			local GetHealth = GetHealth
			local GetMaxHealth = GetMaxHealth
			local GetResourceConsumed = moho.unit_methods.GetResourceConsumed
            local GetEconomyStored = moho.aibrain_methods.GetEconomyStored
			local SetShieldRatio = SetShieldRatio
			local WaitTicks = WaitTicks
			
			local aiBrain = self.Owner:GetAIBrain()
			
            -- If the shield was turned off; use the recharge time before turning back on
            if self.OffHealth >= 0 then
			
                self.Owner:SetMaintenanceConsumptionActive()
				
                self:ChargingUp( 0, self.ShieldEnergyDrainRechargeTime )
                
                -- If the shield has less than full health, allow the shield to begin regening
                if GetHealth(self) < GetMaxHealth(self) and self.RegenRate > 0 then
				
                    self.RegenThread = self:ForkThread(self.RegenStartThread)

                end
				
            end
            
            -- We are no longer turned off
            self.OffHealth = -1
			
            SetShieldRatio( self.Owner, GetHealth(self)/GetMaxHealth(self) )
			
            self.Owner:OnShieldEnabled()
			self:CreateShieldMesh()

            WaitTicks(10)
            
            -- Test in here if we have run out of power
            while true do
			
				WaitTicks(5)
				
				SetShieldRatio( self.Owner, GetHealth(self)/GetMaxHealth(self) )
				
                if GetResourceConsumed( self.Owner ) != 1 and GetEconomyStored(aiBrain, 'ENERGY') < 1 then
					
					break
				end
            end
            
            -- Record the amount of health on the shield here so when the unit tries to turn its shield
            -- back on and off it has the amount of health from before.

            ChangeState(self, self.EnergyDrainRechargeState)
        end,

        IsOn = function(self)
            return true
        end,
		
    },

    -- When manually turned off
    OffState = State {

        Main = function(self)
		
			-- No regen during off state
			if self.RegenThread then
				KillThread(self.RegenThread)
				self.RegenThread = nil
			end

            -- Set the offhealth - this is used basically to let the unit know the unit was manually turned off
      		self.OffHealth = GetHealth(self)

            -- Get rid of the shield bar
            self:UpdateShieldRatio(0)

            self:RemoveShield()
			
    		self.Owner:OnShieldDisabled()

            WaitTicks(10)
			
        end,

        IsOn = function(self)
            return false
        end,
    },

    -- This state happens when the shield has been depleted due to damage
    DamageRechargeState = State {
	
        Main = function(self)

			-- No regen during off state
			if self.RegenThread then
				KillThread(self.RegenThread)
				self.RegenThread = nil
			end
			
            self:RemoveShield()
            
            -- make the unit charge up before gettings its shield back
            self:ChargingUp(0, self.ShieldRechargeTime)
            
            -- Fully charged, get full health
            self:SetHealth(self, GetMaxHealth(self))
            
            ChangeState(self, self.OnState)
			
        end,
		
        IsOn = function(self)
            return false
        end,
    },

    -- This state happens only when the army has run out of power
    EnergyDrainRechargeState = State {
	
        Main = function(self)

			-- No regen during off state
			if self.RegenThread then
				KillThread(self.RegenThread)
				self.RegenThread = nil
			end
			
            self:RemoveShield()
            
            self:ChargingUp(0, self.ShieldEnergyDrainRechargeTime)
            
            -- If the unit is attached to a transport, make sure the shield goes to the off state
            -- so the shield isn't turned on while on a transport
            if not self.Owner:IsUnitState('Attached') then
			
                ChangeState(self, self.OnState)
				
            else
			
                ChangeState(self, self.OffState)
				
            end
			
        end,
        
        IsOn = function(self)
            return false
        end,
		
    },

    DeadState = State {
        Main = function(self)
			self.Dead = true
        end,

        IsOn = function(self)
            return false
        end,
    },
	
}
end -- Do End
