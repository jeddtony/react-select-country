import React, {createContext, useContext, useState} from 'react';

export const CountryContext = createContext();

export const CountryProvider = ({children}) => {
    const [countrySelected, setCountrySelected] = useState(1);

    return (
        <CountryContext.Provider value={{countrySelected, setCountrySelected}}>
            {children}
        </CountryContext.Provider>
    )
}

export const useCountrySelected = () => useContext(CountryContext);